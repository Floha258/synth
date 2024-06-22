from functools import lru_cache
from collections import defaultdict

from pysmt.formula import FormulaManager
from pysmt.shortcuts import BV, BVType, Or, And, BVSGE, BVSLE, BVULE, Solver, Symbol, Implies, LE, EqualsOrIff, Not, \
    BVZExt, NotEquals, FALSE
from pysmt.environment import Environment, get_env
from pysmt.fnode import FNode
from pysmt.typing import BOOL

from cegis import Spec, Func, Prg, no_debug, timer, cegis


class EnumBase:
    def __init__(self, items: set, cons: set[FNode]):
        assert len(items) == len(cons)
        self.cons = cons
        self.item_to_cons = {i: con for i, con in zip(items, cons)}
        self.cons_to_item = {con: i for i, con in zip(items, cons)}

    def __len__(self):
        return len(self.cons)


class EnumSortEnum(EnumBase):
    def __init__(self, name, items):
        w = len(items).bit_length()
        cons = [BV(i, w) for i in range(len(items))]
        self.sort = BVType(w)

        # Add constrains to ensure only valid values can be selected
        lower_constr = BV(0, w)
        higher_constr = BV(len(items) - 1, w)
        self.constraints = Or(And(BVSGE(con, lower_constr), BVSLE(con, higher_constr)) for con in cons)

        super().__init__(items, set(cons))

    def get_from_model_val(self, val):
        return self.cons_to_item[val]

    def add_range_constr(self, solver, var):
        pass

    def translate_enum(self):
        env: Environment = get_env()
        cons_translation: dict[FNode, FNode] = {}
        translated_cons: list[FNode] = []
        # translate cons
        for con in self.cons:
            translated_con = env.formula_manager.normalize(con)
            cons_translation[con] = translated_con
            translated_cons.append(translated_con)
        # put translated cons in cons_to_items and items_to_cons
        for con in self.cons_to_item.keys():
            item = self.cons_to_item[con]
            del self.cons_to_item[con]
            translated_con = cons_translation[con]
            self.cons_to_item[translated_con] = item
            self.item_to_cons[item] = translated_con
        self.cons = translated_cons


def _bv_sort(n):
    return BVType(len(bin(n)) - 2)  # bv sort


class BitVecEnum(EnumBase):
    def __init__(self, name, items: set):
        self.sort = _bv_sort(len(items))
        super().__init__(items, {i for i, _ in enumerate(items)})

    def get_from_model_val(self, val):
        return self.cons_to_item[val.as_long()]

    def add_range_constr(self, solver, var):
        solver.add(BVULE(var, len(self.item_to_cons) - 1))  # Should be unsigned


class SynthN:
    def __init__(self, spec: Spec, ops: list[Func], n_insns, \
                 debug=no_debug, max_const=None, const_set=None, \
                 output_prefix=None, theory=None, reset_solver=True, \
                 opt_no_dead_code=True, opt_no_cse=True, opt_const=True, \
                 opt_commutative=True, opt_insn_order=True, solver_name="z3"):
        """Synthesize a program that computes the given functions.
        Attributes:
        spec: The specification of the program to be synthesized.
        ops: List of operations that can be used in the program.
        n_insn: Number of instructions in the program.
        debug: Debug level. 0: no debug output, >0 more debug output.
        max_const: Maximum number of constants that can be used in the program.
        const_set: Restrict constants to values from this set.
        init_samples: A list of input/output samples that are used to initialize the synthesis process.
        output_prefix: If set to a string, the synthesizer dumps every SMT problem to a file with that prefix.
        theory: A theory to use for the synthesis solver (e.g. QF_FD for finite domains).
        reset_solver: Resets the solver for each counter example.
            For some theories (e.g. FD) incremental solving makes Z3 fall back
            to slower solvers. Setting reset_solver to false prevents that.
        Following search space space pruning optimization flags are available:
        opt_no_dead_code: Disallow dead code.
        opt_no_cse: Disallow common subexpressions.
        opt_const: At most arity-1 operands can be constants.
        opt_commutative: Force order of operands of commutative operators.
        opt_insn_order: Order of instructions is determined by operands.
        Returns:
        A pair (prg, stats) where prg is the synthesized program (or None
        if no program has been found), stats is a list of statistics for each
        iteration of the synthesis loop.
        """
        # TODO: Possibly push new env
        self.orig_spec = spec
        self.spec = spec = spec.translate()
        self.orig_ops = {op.translate(): op for op in ops}
        self.ops = ops = list(self.orig_ops.keys())
        self.n_insns = n_insns

        self.in_tys = spec.in_types
        self.out_tys = spec.out_types
        self.n_inputs = len(self.in_tys)
        self.n_outputs = len(self.out_tys)
        self.out_insn = self.n_inputs + self.n_insns
        self.length = self.out_insn + 1
        max_arity = max(op.arity for op in ops)
        self.arities = [0] * self.n_inputs \
                       + [max_arity] * self.n_insns \
                       + [self.n_outputs]

        # prepare operator enum sort
        self.op_enum = BitVecEnum('Operators', set(ops))

        # create map of types to their id
        types = set(ty for op in ops for ty in op.out_types + op.in_types)
        self.ty_enum = BitVecEnum('Types', types)

        # get the sorts for the variables used in synthesis
        self.ty_sort = self.ty_enum.sort
        self.op_sort = self.op_enum.sort
        self.ln_sort = _bv_sort(self.length - 1)
        self.bl_sort = BOOL

        # set options
        self.d = debug
        self.n_samples = 0
        self.output_prefix = output_prefix
        self.reset_solver = reset_solver

        # setup the synthesis solver
        if theory:
            self.synth_solver = Solver(logic=theory, name=solver_name)
        else:
            self.synth_solver = Solver(name=solver_name)
        self.synth: Solver = Solver(logic=theory, name=solver_name) if theory else Solver(name=solver_name)

        # add well-formedness, well-typedness, and optimization constraints
        self.add_constr_wfp(max_const, const_set)
        self.add_constr_ty()
        self.add_constr_opt(opt_no_dead_code, opt_no_cse, opt_const, \
                            opt_commutative, opt_insn_order)
        self.d(1, 'size', self.n_insns)

    @lru_cache
    def ty_name(ty):
        return str(ty).replace(' ', '_') \
            .replace(',', '_') \
            .replace('(', '_') \
            .replace(')', '_')

    def sample_n(self, n):
        return self.spec.eval.sample_n(n)

    @lru_cache
    def get_var(self, ty, name: str) -> FNode:
        return Symbol(name, ty)

    def var_insn_op(self, insn):
        return self.get_var(self.op_sort, f'insn_{insn}_op')

    def var_insn_opnds_is_const(self, insn):
        for opnd in range(self.arities[insn]):
            yield self.get_var(self.bl_sort, f'insn_{insn}_opnd_{opnd}_is_const')

    def var_insn_op_opnds_const_val(self, insn, opnd_tys):
        for opnd, ty in enumerate(opnd_tys):
            yield self.get_var(ty, f'|insn_{insn}_opnd_{opnd}_{SynthN.ty_name(ty)}_const_val|')

    def var_insn_opnds(self, insn):
        for opnd in range(self.arities[insn]):
            yield self.get_var(self.ln_sort, f'insn_{insn}_opnd_{opnd}')

    def var_insn_opnds_val(self, insn, tys, instance):
        for opnd, ty in enumerate(tys):
            yield self.get_var(ty, f'|insn_{insn}_opnd_{opnd}_{SynthN.ty_name(ty)}_{instance}|')

    def var_outs_val(self, instance):
        for opnd in self.var_insn_opnds_val(self.out_insn, self.out_tys, instance):
            yield opnd

    def var_insn_opnds_type(self, insn):
        for opnd in range(self.arities[insn]):
            yield self.get_var(self.ty_sort, f'insn_{insn}_opnd_type_{opnd}')

    def var_insn_res(self, insn, ty, instance):
        return self.get_var(ty, f'|insn_{insn}_res_{SynthN.ty_name(ty)}_{instance}|')

    def var_insn_res_type(self, insn):
        return self.get_var(self.ty_sort, f'insn_{insn}_res_type')

    def var_input_res(self, insn, instance):
        return self.var_insn_res(insn, self.in_tys[insn], instance)

    def is_op_insn(self, insn):
        return self.n_inputs <= insn < self.length - 1

    def iter_opnd_info(self, insn, tys, instance):
        return zip(tys, \
                   self.var_insn_opnds(insn), \
                   self.var_insn_opnds_val(insn, tys, instance), \
                   self.var_insn_opnds_is_const(insn), \
                   self.var_insn_op_opnds_const_val(insn, tys))

    def iter_opnd_info_struct(self, insn, tys):
        return zip(tys, \
                   self.var_insn_opnds(insn), \
                   self.var_insn_opnds_is_const(insn), \
                   self.var_insn_op_opnds_const_val(insn, tys))

    def add_constr_wfp(self, max_const, const_set):
        solver: Solver = self.synth

        # acyclic: line numbers of uses are lower than line number of definition
        # i.e.: we can only use results of preceding instructions
        for insn in range(self.length):
            for v in self.var_insn_opnds(insn):
                solver.add_assertion(BVULE(v, BV(insn - 1, v.bv_width())))

        # pin operands of an instruction that are not used (because of arity)
        # to the last input of that instruction
        for insn in range(self.n_inputs, self.length - 1):
            opnds = list(self.var_insn_opnds(insn))
            for op, op_id in self.op_enum.item_to_cons.items():
                unused = opnds[op.arity:]
                for opnd in unused:
                    # TODO: Probably replace infix with prefix
                    solver.add_assertion(Implies(self.var_insn_op(insn) == op_id, \
                                                 opnd == opnds[op.arity - 1]))

        # Add a constraint for the maximum amount of constants if specified.
        # The output instruction is exempt because we need to be able
        # to synthesize constant outputs correctly.
        max_const_ran = range(self.n_inputs, self.length - 1)
        if max_const and len(max_const_ran) > 0:
            solver.add_assertion(LE(*[v for insn in max_const_ran \
                                      for v in self.var_insn_opnds_is_const(insn)],
                                    max_const))  # TODO: AtMost replace by LE (is this actually correct????)

        # limit the possible set of constants if desired
        if const_set:
            const_map = defaultdict(list)
            for c in const_set:
                env: Environment = get_env()
                c: FNode = env.formula_manager.normalize(c)
                const_map[c.get_type()].append(c)
            for insn in range(self.n_inputs, self.length):
                for op, op_id in self.op_enum.item_to_cons.items():
                    for ty, _, _, cv in self.iter_opnd_info_struct(insn, op.in_types):
                        solver.add_assertion(Or([cv == v for v in const_map[ty]]))

    def add_constr_ty(self):
        if len(self.ty_enum) <= 1:
            # we don't need constraints if there is only one type
            return

        solver: Solver = self.synth
        # for all instructions that get an op
        # add constraints that set the type of an instruction's operand
        # and the result type of an instruction
        types = self.ty_enum.item_to_cons
        for insn in range(self.n_inputs, self.length - 1):
            for op, op_id in self.op_enum.item_to_cons.items():
                # add constraints that set the result type of each instruction
                solver.add_assertion(Implies(EqualsOrIff(self.var_insn_op(insn), op_id), \
                                             EqualsOrIff(self.var_insn_res_type(insn), types[op.out_type])))
                # add constraints that set the type of each operand
                for op_ty, v in zip(op.in_types, self.var_insn_opnds_type(insn)):
                    solver.add_assertion(Implies(EqualsOrIff(self.var_insn_op(insn), op_id), \
                                                 EqualsOrIff(v, types[op_ty])))

        # define types of inputs
        for inp, ty in enumerate(self.in_tys):
            solver.add_assertion(EqualsOrIff(self.var_insn_res_type(inp), types[ty]))

        # define types of outputs
        for v, ty in zip(self.var_insn_opnds_type(self.out_insn), self.out_tys):
            solver.add_assertion(EqualsOrIff(v, types[ty]))

        # constrain types of outputs
        for insn in range(self.n_inputs, self.length):
            for other in range(0, insn):
                for opnd, c, ty in zip(self.var_insn_opnds(insn), \
                                       self.var_insn_opnds_is_const(insn), \
                                       self.var_insn_opnds_type(insn)):
                    solver.add_assertion(Implies(Not(c), Implies(EqualsOrIff(opnd, other), \
                                                                 EqualsOrIff(ty, self.var_insn_res_type(other)))))
            self.ty_enum.add_range_constr(solver, self.var_insn_res_type(insn))

    def add_constr_opt(self, opt_no_dead_code, opt_no_cse, opt_const, opt_commutative, opt_insn_order):
        solver: Solver = self.synth

        def opnd_set(insn):
            ext = self.length - self.ln_sort.size()
            assert ext >= 0
            res = BV(0, self.length)
            one = BV(1, self.length)
            for opnd in self.var_insn_opnds(insn):
                res |= one << BVZExt(opnd, ext)
            return res

        if opt_insn_order:
            for insn in range(self.n_inputs, self.out_insn - 1):
                solver.add_assertion(BVULE(opnd_set(insn), opnd_set(insn + 1)))

        for insn in range(self.n_inputs, self.out_insn):
            op_var = self.var_insn_op(insn)
            for op, op_id in self.op_enum.item_to_cons.items():
                # if operator is commutative, force the operands to be in ascending order
                if opt_commutative and op.is_commutative:
                    opnds = list(self.var_insn_opnds(insn))
                    c = [BVULE(l, u) for l, u in zip(opnds[:op.arity - 1], opnds[1:])]
                    # TODO: This was somehow not equals prior? Also requires ctx in og
                    solver.add_assertion(Implies(EqualsOrIff(op_var, op_id), And(c)))

                if opt_const:
                    vars = [v for v in self.var_insn_opnds_is_const(insn)][:op.arity]
                    assert len(vars) > 0
                    if op.arity == 2 and op.is_commutative:
                        # Binary commutative operators have at most one constant operand
                        # Hence, we pin the first operand to me non-constant
                        false = FALSE()
                        solver.add_assertion(Implies(EqualsOrIff(op_var, op_id), EqualsOrIff(vars[0], false)))
                    else:
                        # Otherwise, we require that at least one operand is non-constant
                        solver.add_assertion(Implies(EqualsOrIff(op_var, op_id), Not(And(vars))))

            # Computations must not be replicated: If an operation appears again
            # in the program, at least one of the operands must be different from
            # a previous occurrence of the same operation.
            if opt_no_cse:
                for other in range(self.n_inputs, insn):
                    un_eq = [NotEquals(p, q) for p, q in zip(self.var_insn_opnds(insn), self.var_insn_opnds(other))]
                    assert len(un_eq) > 0
                    solver.add_assertion(Implies(EqualsOrIff(op_var, self.var_insn_op(other)), Or(un_eq)))

        # no dead code: each produced value is used
        if opt_no_dead_code:
            for prod in range(self.n_inputs, self.length):
                opnds = [EqualsOrIff(prod, v) for cons in range(prod + 1, self.length) for v in self.var_insn_opnds(cons)]

                if len(opnds) > 0:
                    solver.add_assertion(Or(opnds))

    def synth_with_new_samples(self, samples):
        ops = self.ops
        spec = self.spec
        manager: FormulaManager = get_env().formula_manager
        samples = [[manager.normalize(v) for v in s] for s in samples]

        def add_constr_conn(solver: Solver, insn, tys, instance):
            for ty, l, v, c, cv in self.iter_opnd_info(insn, tys, instance):
                # if the operand is a constant, its value is the constant value
                solver.add_assertion(Implies(c, EqualsOrIff(v, cv)))
                # else, for other each instruction preceding it ...
                for other in range(insn):
                    r = self.var_insn_res(other, ty, instance)
                    # ... the operand is equal to the result of the instruction
                    solver.add_assertion(Implies(Not(c), Implies(EqualsOrIff(l, other), EqualsOrIff(v, r))))

        def add_constr_instance(solver: Solver, instance):
            # for all instructions that get an op
            for insn in range(self.n_inputs, self.length - 1):
                # add constraints to select the proper operation
                op_var = self.var_insn_op(insn)
                for op, op_id in self.op_enum.item_to_cons.items():
                    res = self.var_insn_res(insn, op.out_type, instance)
                    opnds = list(self.var_insn_opnds_val(insn, op.in_types, instance))
                    [precond], [phi] = op.instantiate([res], opnds)
                    solver.add_assertion(Implies(EqualsOrIff(op_var, op_id), And([precond, phi])))
                # connect values of operands to values of corresponding results
                for op in ops:
                    add_constr_conn(solver, insn, op.in_types, instance)
            # add connection constraints for output instruction
            add_constr_conn(solver, self.out_insn, self.out_tys, instance)

        def add_constr_io_sample(solver: Solver, instance, in_vals, out_vals):
            # add input value constraints
            assert len(in_vals) == self.n_inputs and len(out_vals) == self.n_outputs
            for inp, val in enumerate(in_vals):
                assert not val is None
                res = self.var_input_res(inp, instance)
                solver.add_assertion(EqualsOrIff(res, val))
            for out, val in zip(self.var_outs_val(instance), out_vals):
                assert not val is None
                solver.add_assertion(EqualsOrIff(out, val))

        def add_constr_io_spec(solver: Solver, instance, in_vals):
            # add input value constraints
            assert len(in_vals) == self.n_inputs
            assert all(not val is None for val in in_vals)
            for inp, val in enumerate(in_vals):
                solver.add_assertion(EqualsOrIff(val, self.var_input_res(inp, instance)))
            outs = [v for v in self.var_outs_val(instance)]
            preconds, phis = spec.instantiate(outs, in_vals)
            for pre, phi in zip(preconds, phis):
                solver.add_assertion(Implies(pre, phi))

        def create_prg(model):
            def prep_opnds(insn, tys):
                for _, opnd, c, cv in self.iter_opnd_info_struct(insn, tys):
                    if model[c].is_true():
                        assert not model[c] is None
                        manager = get_env().formula_manager
                        yield (True, manager.normalize(model[cv]))
                    else:
                        # TODO: Search up as long equivalent in pysmt
                        yield (False, model[opnd].as_long())

            insns = []
            for insn in range(self.n_inputs, self.length - 1):
                val = model[self.var_insn_op(insn)]
                op = self.op_enum.get_from_model_val(val)
                opnds = [v for v in prep_opnds(insn, op.in_types)]
                insns += [(self.orig_ops[op], opnds)]
            outputs = [v for v in prep_opnds(self.out_insn, self.out_tys)]
            return Prg(self.orig_spec, insns, outputs)

        def write_smt2(*args):
            s = self.synth_solver
            # TODO: This code is probably not needed cause in pysmt we will always have a solver class
            # if not type(s) is Solver:
            #     # TODO: Needs to get solvername from somewhere
            #     s = Solver()
            #     s.add(self.synth_solver)
            if self.output_prefix:
                filename = f'{self.output_prefix}_{"_".join(str(a) for a in args)}.smt2'
                with open(filename, 'w') as f:
                    print(s.to_smt2(), file=f)

        # main synthesis algorithm.
        # 1) set up counter examples
        for sample in samples:
            # add a new instance of the specification for each sample
            add_constr_instance(self.synth, self.n_samples)
            if self.spec.is_deterministic and self.spec.is_total:
                # if the specification is deterministic and total we can
                # just use the specification to sample output values and
                # include them in the counterexample constraints.
                out_vals = self.spec.eval(sample)
                add_constr_io_sample(self.synth, self.n_samples, sample, out_vals)
            else:
                # if the spec is not deterministic or total, we have to
                # express the output of the specification implicitly by
                # the formula of the specification.
                add_constr_io_spec(self.synth, self.n_samples, sample)
            self.n_samples += 1
        write_smt2('synth', self.n_insns, self.n_samples)
        stat = {}
        # TODO: Do we need reset solver if we can't make use of the z3 optimizations?
        # if self.reset_solver:
        #     self.synth_solver.reset_assertions()
        #     self.synth_solver.add_assertions([assertion for assertion in self.synth.assertions])
        with timer() as elapsed:
            res = self.synth_solver.solve()
            synth_time = elapsed()
            # d(3, synth_solver.statistics())
            self.d(2, f'synth time: {synth_time / 1e9:.3f}')
            stat['synth_time'] = synth_time
        if res:
            # if sat, we found location variables
            m = self.synth_solver.get_model()
            prg = create_prg(m)
            self.d(4, 'model: ', m)
            return prg, stat
        else:
            return None, stat


def synth(spec: Spec, ops: list[Func], iter_range, n_samples=1, **args):
    """Synthesize a program that computes the given functions.

    Attributes:
    spec: List of functions that the program has to compute.
        All functions have to have the same number of operands and
        have to agree on their operand types.
    ops: List of operations that can be used in the program.
    iter_range: Range of program lengths that are tried.
    n_samples: Number of initial I/O samples to give to the synthesizer.
    args: arguments passed to the synthesizer

    Returns:
    A tuple (prg, stats) where prg is the synthesized program (or None
    if no program has been found) and stats is a list of statistics for each
    iteration of the synthesis loop.
    """

    all_stats = []
    init_samples = spec.eval.sample_n(n_samples)
    for n_insns in iter_range:
        with timer() as elapsed:
            synthesizer = SynthN(spec, ops, n_insns, **args)
            prg, stats = cegis(spec, synthesizer, init_samples=init_samples, \
                               debug=synthesizer.d)
            all_stats += [ { 'time': elapsed(), 'iterations': stats } ]
            if not prg is None:
                return prg, all_stats
    return None, all_stats


