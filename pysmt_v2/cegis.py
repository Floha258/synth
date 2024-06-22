import sys
import time
from contextlib import contextmanager
from functools import cached_property
from itertools import combinations as comb
from itertools import permutations as perm

from pysmt.environment import push_env, pop_env
from pysmt.fnode import FNode
from pysmt.formula import FormulaManager
from pysmt.shortcuts import EqualsOrIff, Or, Not, get_env, TRUE, FreshSymbol, And, NotEquals, Solver
from pysmt.typing import BOOL

solverName = 'z3'


def _eval_model(solver: Solver, vars):
    m = solver.get_model()
    return [m.get_value(v, model_completion=True) for v in vars]


class Eval:
    def __init__(self, inputs: list[FNode], outputs: list[FNode], solver: Solver):
        self.inputs = inputs
        self.outputs = outputs
        self.solver = solver

    def __call__(self, input_vals):
        s = self.solver
        s.push()
        for var, val in zip(self.inputs, input_vals):
            s.add_assertion(EqualsOrIff(var, val))
        assert s.solve()
        res = _eval_model(s.get_model(), self.outputs)
        s.pop()
        return res

    def sample_n(self, n):
        """Samples the specification n times.
           The result is a list that contains n lists of
           input values that are unique.
           The list may contain less than n elements if there
           are less than n unique inputs.
        """
        res = []
        s = self.solver
        s.push()
        for _ in range(n):
            if s.solve():
                ins = _eval_model(s, self.inputs)
                res += [ins]
                s.add_assertion(Or([Not(EqualsOrIff(v, iv)) for v, iv in zip(self.inputs, ins)]))
            else:
                assert len(res) > 0, 'cannot evaluate'
        s.pop()
        return res


class Spec:
    def _collect_vars(expr: FNode):
        res = set()

        def collect(expr: FNode):
            # if len(expr.children()) == 0 and expr.decl().kind() == Z3_OP_UNINTERPRETED:
            if len(expr.args()) == 0 and expr.node_type() == 7:  # 7 for symbol
                res.add(expr)
            else:
                for c in expr.args():
                    collect(c)

        collect(expr)
        return res

    def __init__(self, name: str, phis: list[FNode], outputs: list[FNode],
                 inputs: list[FNode], preconds: list[BOOL] = None):  # TODO Check z3 code
        """
        Create a specification.

        A specification object represents n specifications each given
        by a Z3 expression (phis).

        inputs is the list of input variables that the n formulas use.
        outputs is the list of output variables that the n formulas use.
        There must be as many variables in outputs as there are formulas in phis.
        Each specification can optionally have a precondition (preconds)
        to express partial functions.
        If preconds is None, all preconditions are True.

        Specifications can be non-deterministic.

        Attributes:
        name: Name of the specification.
        phis: List of Z3 expressions of which each represents
            the specification of the i-th function.
        outputs: List of output variables in phi.
        inputs: List of input variables in phi.
        preconds: A precondition for each output
            (if None, all preconditions are True)

        Note that the names of the variables don't matter because when
        used in the synthesis process their names are substituted by internal names.
        """
        assert len(phis) > 0, 'need at least one output'
        assert len(phis) == len(outputs), \
            'number of outputs must match number of specifications'
        assert preconds is None or len(preconds) == len(outputs), \
            'number of preconditions must match'
        self.env = get_env()
        self.name = name
        self.arity = len(inputs)
        self.inputs = inputs
        self.outputs = outputs
        self.phis = phis
        self.preconds = preconds if preconds else [TRUE() for _ in outputs]
        self.vars = set().union(*[Spec._collect_vars(phi) for phi in phis])
        all_vars = outputs + inputs
        assert len(set(all_vars)) == len(all_vars), 'outputs and inputs must be unique'
        assert self.vars <= set(all_vars), \
            f'phi must use only out and in variables: {self.vars} vs {all_vars}'
        for pre, phi, out in zip(self.preconds, self.phis, self.outputs):
            assert Spec._collect_vars(pre) <= set(self.inputs), \
                f'precondition must use input variables only'
            assert Spec._collect_vars(phi) <= set(inputs + outputs), \
                f'i-th spec must use only i-th out and input variables {phi}'

    def __str__(self):
        return self.name

    # Uses the formulaManager of the current env, no env as parameter needed
    def translate(self):
        formulaManager = get_env().formula_manager
        ins = [formulaManager.normalize(x) for x in self.inputs]
        outs = [formulaManager.normalize(x) for x in self.outputs]
        pres = [formulaManager.normalize(x) for x in self.preconds]
        phis = [formulaManager.normalize(x) for x in self.phis]
        return Spec(self.name, phis, outs, ins, pres)

    @cached_property
    def eval(self):
        s = Solver(name=solverName)
        for p in self.phis:
            s.add_assertion(p)
        return Eval(self.inputs, self.outputs, s)

    @cached_property
    def out_types(self):
        return [v.get_type() for v in self.outputs]

    @cached_property
    def in_types(self):
        return [v.get_type() for v in self.inputs]

    @cached_property
    def is_total(self):
        solver = Solver(environment=self.env, name=solverName)
        solver.add_assertion(Or([Not(p) for p in self.preconds]))
        return not solver.solve()

    @cached_property
    def is_deterministic(self):
        solver = Solver(environment=self.env, name=solverName)
        ins = [FreshSymbol(ty) for ty in self.in_types]
        outs = [FreshSymbol(ty) for ty in self.out_types]
        _, phis = self.instantiate(outs, ins)
        solver.add_assertion(And([p for p in self.preconds]))
        for p in self.phis:
            solver.add_assertion(p)
        for p in phis:
            solver.add_assertion(p)
        solver.add_assertion(And([EqualsOrIff(a, b) for a, b in zip(self.inputs, ins)]))
        solver.add_assertion(Or([Not(EqualsOrIff(a, b)) for a, b in zip(self.outputs, outs)]))
        return not solver.solve()  # unsat

    def instantiate(self, outs: list[FNode], ins: list[FNode]):
        # pop_env()
        # pop_env()
        # pop_env()
        # pop_env()
        self_outs: list[FNode] = self.outputs
        self_ins: list[FNode] = self.inputs
        assert len(outs) == len(self_outs)
        assert len(ins) == len(self_ins)
        # assert all(x.ctx == y.ctx for x, y in zip(self_outs + self_ins, outs + ins))
        # [substitute(phi, list(zip(self_outs + self_ins, outs + ins))) for phi in self.phis]
        phis: list[FNode] = []
        self_outs_ins = []
        manager: FormulaManager = get_env().formula_manager
        for node in (self_outs + self_ins):
            self_outs_ins.append(manager.normalize(node))
        outs_ins = []
        for node in (outs + ins):
            outs_ins.append(manager.normalize(node))
        for phi in self.phis:
            phis.append(phi.substitute(dict(zip(self_outs_ins, outs_ins))))
        pres = []
        for p in self.preconds:
            pres.append(p.substitute(dict(zip(self_ins, outs_ins[0:(len(ins) - 1)]))))
        # push_env()
        # push_env()
        # push_env()
        # push_env()
        return pres, phis


class Func(Spec):
    def __init__(self, name, phi, precond=TRUE(), inputs=[]):
        """Creates an Op from a Z3 expression.

        Attributes:
        name: Name of the operator.
        phi: Z3 expression that represents the semantics of the operator.
        precond: Z3 expression that represents the precondition of the operator.
        inputs: List of input variables in phi. If [] is given, the inputs
            are taken in lexicographical order.
        """
        input_vars = Spec._collect_vars(phi)
        # if no inputs are specified, we take the identifiers in
        # lexicographical order. That's just a convenience
        if len(inputs) == 0:
            inputs = sorted(input_vars, key=lambda v: str(v))
        # create Z3 variable of a given sort
        res_ty = phi.get_type()  # phi.sort
        self.precond = precond
        self.func = phi
        out = FreshSymbol(res_ty)
        super().__init__(name, [EqualsOrIff(out, phi)], [out], inputs, preconds=[precond])

    @cached_property
    def is_deterministic(self):
        return True

    def translate(self):
        formulaManager = get_env().formula_manager
        ins = [formulaManager.normalize(i) for i in self.inputs]
        normalized_func = formulaManager.normalize(self.func)
        normalized_precond = formulaManager.normalize(self.precond)
        return Func(self.name, normalized_func,
                    normalized_precond, ins)

    @cached_property
    def out_type(self):
        return self.out_types[0]

    @cached_property
    def is_commutative(self):
        # if the operator inputs have different types, it cannot be commutative
        if len(set(v.get_type() for v in self.inputs)) > 1 or len(self.inputs) > 3:
            return False
        push_env()
        env = get_env()
        formulaManager = env.formula_manager
        precond = formulaManager.normalize(self.precond)
        func = formulaManager.normalize(self.func)
        ins = [formulaManager.normalize(x) for x in self.inputs]
        substituter = env.substituter
        subst = lambda f, i: substituter.substitute(f, dict(zip(ins, i)))
        fs = [And([subst(precond, a), subst(precond, b), \
                   NotEquals(subst(func, a), subst(func, b))]) \
              for a, b in comb(perm(ins), 2)]
        s = Solver(name=solverName)
        s.add_assertion(Or(fs))  # missing context
        res = s.solve()
        pop_env()
        return not res


class Prg:
    def __init__(self, spec: Spec, insns: list[FNode], outputs: list[FNode]):
        """Creates a program.

        Attributes:
        input_names: list of names of the inputs
        insns: List of instructions.
            This is a list of pairs where each pair consists
            of an Op and a list of pairs that denotes the arguments to
            the instruction. The first element of the pair is a boolean
            that indicates whether the argument is a constant or not.
            The second element is either the variable number of the
            operand or the constant value of the operand.
        outputs: List of variable numbers that constitute the output.
        """
        self.spec = spec
        self.insns = insns
        self.outputs = outputs
        self.output_names = [str(v) for v in spec.outputs]
        self.input_names = [str(v) for v in spec.inputs]
        # this map gives for every temporary/input variable
        # which output variables are set to it
        self.output_map = {}
        for (is_const, v), name in zip(outputs, self.output_names):
            if not is_const:
                self.output_map.setdefault(v, []).append(name)

    def var_name(self, i):
        if i < len(self.input_names):
            return self.input_names[i]
        elif i in self.output_map:
            return self.output_map[i][0]
        else:
            return f'x{i}'

    def __len__(self):
        return len(self.insns)

    def eval_clauses(self):
        spec = self.spec
        vars = list(spec.inputs)
        n_inputs = len(vars)

        def get_val(p):
            is_const, v = p
            return v if is_const else vars[v]

        for i, (insn, opnds) in enumerate(self.insns):
            subst = [(i, get_val(p)) \
                     for i, p in zip(insn.inputs, opnds)]
            res = FreshSymbol(self.var_name(i + n_inputs), insn.func.get_type())
            vars.append(res)
            substituter = get_env().substituter
            yield res == substituter.substitute(dict(zip(insn.func, subst)))
        for o, p in zip(spec.outputs, self.outputs):
            yield o == get_val(p)

        @cached_property
        def eval(self):
            s = Solver(name=solverName)
            for p in self.eval_clauses():
                s.add_assertion(p)
            return Eval(self.spec.inputs, self.spec.outputs, s)

    def __str__(self):
        all_names = self.input_names + self.output_names + \
                    [names[0] for names in self.output_map.values()]
        max_len = max(map(len, all_names))
        n_inputs = len(self.input_names)
        jv = lambda args: ', '.join(str(v) if c else self.var_name(v) for c, v in args)
        res = []
        for i, names in self.output_map.items():
            if i < n_inputs:
                res += [f'{n:{max_len}} = {self.input_names[i]}' for n in names]
        for i, (op, args) in enumerate(self.insns):
            y = self.var_name(i + n_inputs)
            res += [f'{y:{max_len}} = {op.name}({jv(args)})']
        for names in self.output_map.values():
            for n in names[1:]:
                res += [f'{n:{max_len}} = {names[0]}']
        for n, (is_const, v) in zip(self.output_names, self.outputs):
            if is_const:
                res += [f'{n:{max_len}} = {v}']
        return '\n'.join(res)

    def print_graphviz(self, file):
        constants = {}

        def print_arg(node, i, is_const, v):
            if is_const:
                if not v in constants:
                    constants[v] = f'const{len(constants)}'
                    print(f'  {constants[v]} [label="{v}"];')
                v = constants[v]
            print(f'  {node} -> {v} [label="{i}"];')

        save_stdout, sys.stdout = sys.stdout, file
        n_inputs = len(self.input_names)
        print(f"""digraph G {{
  rankdir=BT
  {{
    rank = same;
    edge[style=invis];
    rankdir = LR;
""")
        for i, inp in enumerate(self.input_names):
            print(f'    {i} [label="{inp}"];')
        print(f"""
    {' -> '.join([str(i) for i in range(n_inputs)])};
  }}""")

        for i, (op, args) in enumerate(self.insns):
            node = i + n_inputs
            print(f'  {node} [label="{op.name}",ordering="out"];')
            for i, (is_const, v) in enumerate(args):
                print_arg(node, i, is_const, v)
        print(f'  return [label="return",ordering="out"];')
        for i, (is_const, v) in enumerate(self.outputs):
            print_arg('return', i, is_const, v)
        print('}')
        sys.stdout = save_stdout


@contextmanager
def timer():
    start = time.perf_counter_ns()
    yield lambda: time.perf_counter_ns() - start


def no_debug(level, *args):
    pass


def cegis(spec: Spec, synth, init_samples=[], debug=no_debug):
    d = debug

    samples = init_samples if init_samples else spec.eval.sample_n(1)
    assert len(samples) > 0, 'need at least 1 initial sample'

    # set up the verification constraint
    verif = Solver(name=solverName)
    verif.add_assertions(Or([And([pre, Not(phi)]) for pre, phi in zip(spec.preconds, spec.phis)]))

    stats = []
    i = 0

    while True:
        stat = {}
        stats += [stat]
        old_i = i

        for sample in samples:
            if len(sample_str := str(sample)) < 50:
                sample_out = sample_str
            else:
                sample_out = sample_str[:50] + '...'
            d(1, 'sample', i, sample_out)
            i += 1

        samples_str = f'{i - old_i}' if i - old_i > 1 else old_i

        # call the synthesizer with more counter-examples
        prg, synth_stat = synth.synth_with_new_samples(samples)
        stat.update(synth_stat)

        if prg:
            # we got a program, so check if it is correct
            stat['prg'] = str(prg).replace('\n', '; ')
            d(2, 'program:', stat['prg'])

            # push a new verification solver state
            # and add equalities that evaluate the program
            verif.push()
            for c in prg.eval_clauses():
                verif.add_assertion(c)

            d(5, 'verif', samples_str, verif)
            with timer() as elapsed:
                res = verif.solve()
                verif_time = elapsed()
            stat['verif_time'] = verif_time
            d(2, f'verif time {verif_time / 1e9:.3f}')

            if res:
                # there is a counterexample, reiterate
                m = verif.get_model()
                samples = [_eval_model(m, spec.inputs)]
                d(4, 'verification model', m)
                d(4, 'verif sample', samples[0])
                verif.pop()
            else:
                verif.pop()
                # we found no counterexample, the program is therefore correct
                d(1, 'no counter example found')
                return prg, stats

        else:
            d(1, f'synthesis failed')
            return None, stats
