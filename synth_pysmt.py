#! /usr/bin/env python3
import math
import random
import itertools
import sys
import time
import json
import re

from itertools import combinations as comb
from itertools import permutations as perm
from functools import cached_property, lru_cache

from contextlib import contextmanager

from pysmt.environment import push_env, Environment
from pysmt.shortcuts import *
from pysmt.typing import *


# from typing import Any

# from z3 import *


# def_ctx = Int('dummy').ctx

def _collect_vars(expr):
    res = set()

    def collect(expr):
        # if len(expr.children()) == 0 and expr.decl().kind() == Z3_OP_UNINTERPRETED:
        if len(expr.args()) == 0 and expr.node_type() == 7:  # 7 for symbol
            res.add(expr)
        else:
            for c in expr.args():
                collect(c)

    collect(expr)
    return res


class Spec:
    def __init__(self, name: str, phis, outputs,
                 inputs, preconds: list[BOOL] = None):  # TODO Check z3 code
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
        # self.ctx = phis[0].ctx
        self.name = name
        self.arity = len(inputs)
        self.inputs = inputs
        self.outputs = outputs
        self.phis = phis
        self.preconds = preconds if preconds else [TRUE() for _ in outputs]
        self.vars = set().union(*[_collect_vars(phi) for phi in phis])
        all_vars = outputs + inputs
        assert len(set(all_vars)) == len(all_vars), 'outputs and inputs must be unique'
        assert self.vars <= set(all_vars), \
            f'phi must use only out and in variables: {self.vars} vs {all_vars}'
        for pre, phi, out in zip(self.preconds, self.phis, self.outputs):
            assert _collect_vars(pre) <= set(self.inputs), \
                f'precondition must use input variables only'
            assert _collect_vars(phi) <= set(inputs + outputs), \
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
    def out_types(self):
        return [v.sort() for v in self.outputs]

    @cached_property
    def in_types(self):
        return [v.sort() for v in self.inputs]

    @cached_property
    def is_total(self):
        # Create a new environment, no need to save it, the solver automatically uses it
        push_env()
        solver = Solver()
        spec = self.inputs
        solver.add(Or([Not(p) for p in spec.preconds]))
        return solver.check() == False  # unsatisfiable

    @cached_property
    def is_deterministic(self):
        # Create a new environment, no need to save it, the solver automatically uses it
        push_env()
        solver = Solver()
        spec = self.translate()
        ins = []
        for ty in self.inputs:
            ins.append(INT(ty))
        outs = []
        for ty in self.outputs:
            outs.append(INT(ty))
        _, phis = spec.instantiate(outs, ins)
        solver.add(And([p for p in spec.preconds]))
        for p in spec.phis:
            solver.add(p)
        for p in phis:
            solver.add(p)
        solver.add(And([a == b for a, b in zip(self.inputs, ins)]))
        solver.add(Or([a != b for a, b in zip(self.outputs, outs)]))
        return solver.check() == False  # unsat

    def instantiate(self, outs, ins):
        self_outs = self.outputs
        self_ins = self.inputs
        assert len(outs) == len(self_outs)
        assert len(ins) == len(self_ins)
        assert all(x.ctx == y.ctx for x, y in zip(self_outs + self_ins, outs + ins))
        # [substitute(phi, list(zip(self_outs + self_ins, outs + ins))) for phi in self.phis]
        phis = []
        for phi in self.phis:
            phis.append(phi.substitue(list(zip(self_outs + self_ins, outs + ins))))
        pres = []
        for p in self.preconds:
            pres.append(p.substitute(list(zip(self_ins, ins))))
        return pres, phis


class Func(Spec):
    def __init__(self, name, phi, precond=Bool(True), inputs=[]):
        """Creates an Op from a Z3 expression.

        Attributes:
        name: Name of the operator.
        phi: Z3 expression that represents the semantics of the operator.
        precond: Z3 expression that represents the precondition of the operator.
        inputs: List of input variables in phi. If [] is given, the inputs
            are taken in lexicographical order.
        """
        input_vars = _collect_vars(phi)
        # if no inputs are specified, we take the identifiers in
        # lexicographical order. That's just a convenience
        if len(inputs) == 0:
            inputs = sorted(input_vars, key=lambda v: str(v))
        # check if precondition uses only variables that are in phi
        assert _collect_vars(precond) <= input_vars, \
            'precondition uses variables that are not in phi'
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
        return Func(self.name, self.func.translate(),
                    self.precond.translate(), ins)

    @cached_property
    def out_type(self):
        return self.out_types[0]

    @cached_property
    def is_commutative(self):
        # if the operator inputs have different sorts, it cannot be commutative
        if len(set(v.sort() for v in self.inputs)) > 1:
            return False
        # ctx = Context()
        push_env()
        env = get_env()
        precond = self.precond.translate()
        func = self.func.translate()
        formulaManager = env.formula_manager()
        ins = [formulaManager.normalize(x) for x in self.inputs]
        substituter = env.substituter()
        subst = lambda f, i: substituter.substitute(f, dict(zip(ins, i)))
        fs = [And([subst(precond, a), subst(precond, b), \
                   subst(func, a) != subst(func, b)]) \
              for a, b in comb(perm(ins), 2)]
        s = Solver()
        s.add_assertion(Or(fs))  # missing context
        return s.is_unsat()


class Prg:
    def __init__(self, input_names, insns, outputs):
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
        self.input_names = input_names
        self.insns = insns
        self.outputs = outputs

    def var_name(self, i):
        return self.input_names[i] if i < len(self.input_names) else f'x{i}'

    def __len__(self):
        return len(self.insns)

    def __str__(self):
        n_inputs = len(self.input_names)
        jv = lambda args: ', '.join(str(v) if c else self.var_name(v) for c, v in args)
        res = ''.join(f'{self.var_name(i + n_inputs)} = {op.name}({jv(args)})\n' \
                      for i, (op, args) in enumerate(self.insns))
        return res + f'return({jv(self.outputs)})'

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


class EnumBase:
    def __init__(self, items, cons):
        assert len(items) == len(cons)
        self.cons = cons
        self.item_to_cons = {i: con for i, con in zip(items, cons)}
        self.cons_to_item = {con: i for i, con in zip(items, cons)}

    def __len__(self):
        return len(self.cons)


class EnumSortEnum(EnumBase):
    def __init__(self, name, items, ctx):
        self.sort, cons = BVType([str(i) for i in items], name)
        super().__init__(items, cons)

    def get_from_model_val(self, val):
        return self.cons_to_item[val]

    def add_range_constr(self, solver, var):
        pass


def _bv_sort(n, ctx):
    return BVType(len(bin(n)) - 2)  # bv sort


class BitVecEnum(EnumBase):
    def __init__(self, name, items, ctx):
        self.sort = _bv_sort(len(items), ctx)
        super().__init__(items, [i for i, _ in enumerate(items)])

    def get_from_model_val(self, val):
        return self.cons_to_item[val.as_long()]

    def add_range_constr(self, solver, var):
        solver.add(LE(var, len(self.item_to_cons) - 1))  # Should be unsigned


@contextmanager
def timer():
    start = time.process_time_ns()
    yield lambda: time.process_time_ns() - start


def _eval_model(solver, vars):
    m = solver.model()
    e = lambda v: m.evaluate(v, model_completion=True)
    return [e(v) for v in vars]


class SpecWithSolver:
    def __init__(self, spec: Spec, ops: list[Func], logic):
        self.spec = spec = spec.translate()
        self.ops = ops = [op.translate() for op in ops]

        # prepare operator enum sort
        self.op_enum = EnumSortEnum('Operators', ops)

        # create map of types to their id
        types = set(ty for op in ops for ty in op.out_types + op.in_types)
        self.ty_enum = EnumSortEnum('Types', types)

        # prepare verification solver
        self.verif = Solver(logic=logic)
        self.eval = Solver(logic=logic)
        self.inputs = spec.inputs
        self.outputs = spec.outputs

        self.verif.add(Or([And([pre, Not(phi)]) \
                           for pre, phi in zip(spec.preconds, spec.phis)]))
        for phi in spec.phis:
            self.eval.add(phi)

    def eval_spec(self, input_vals):
        s = self.eval
        s.push()
        for var, val in zip(self.inputs, input_vals):
            s.add(var == val)
        res = s.check()
        assert is_sat(res)
        res = _eval_model(s, self.outputs)
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
        s = self.eval
        s.push()
        for i in range(n):
            c = s.check()
            if is_sat(c):
                assert len(res) > 0, 'must have sampled the spec at least once'
                break
            m = s.model()
            ins = _eval_model(s, self.inputs)
            res += [ins]
            s.add(Or([v != iv for v, iv in zip(self.inputs, ins)]))
        s.pop()
        return res

    def synth_n(self, n_insns, \
                debug=0, max_const=None, init_samples=[], \
                output_prefix=None, theory=None, reset_solver=True, \
                opt_no_dead_code=True, opt_no_cse=True, opt_const=True, \
                opt_commutative=True, opt_insn_order=True):
        """Synthesize a program that computes the given functions.

        Attributes:
        spec: The specification of the program to be synthesized.
        ops: List of operations that can be used in the program.
        n_insn: Number of instructions in the program.
        debug: Debug level. 0: no debug output, >0 more debug output.
        max_const: Maximum number of constants that can be used in the program.
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

        # A debug function that prints only if the debug level is high enough
        def d(level, *args):
            if debug >= level:
                print(*args)

        d(1, 'size', n_insns)

        ops = self.ops
        ctx = self.ctx
        spec = self.spec
        in_tys = spec.in_types
        out_tys = spec.out_types
        n_inputs = len(in_tys)
        n_outputs = len(out_tys)
        out_insn = n_inputs + n_insns
        length = out_insn + 1

        max_arity = max(op.arity for op in ops)
        arities = [0] * n_inputs + [max_arity] * n_insns + [n_outputs]

        # get the sorts for the variables used in synthesis
        ty_sort = self.ty_enum.sort
        op_sort = self.op_enum.sort
        ln_sort = _bv_sort(length, ctx)
        bl_sort = PySMTType()

        # get the verification solver and its input and output variables
        eval_ins = self.inputs
        eval_outs = self.outputs
        verif = self.verif

        @lru_cache
        def get_var(ty, name):
            # assert ty.ctx == ctx
            return Symbol(name, ty)

        @lru_cache
        def ty_name(ty):
            return str(ty).replace(' ', '_') \
                .replace(',', '_') \
                .replace('(', '_') \
                .replace(')', '_')

        def var_insn_op(insn):
            return get_var(op_sort, f'insn_{insn}_op')

        def var_insn_opnds_is_const(insn):
            for opnd in range(arities[insn]):
                yield get_var(bl_sort, f'insn_{insn}_opnd_{opnd}_is_const')

        def var_insn_op_opnds_const_val(insn, opnd_tys):
            for opnd, ty in enumerate(opnd_tys):
                yield get_var(ty, f'insn_{insn}_opnd_{opnd}_{ty_name(ty)}_const_val')

        def var_insn_opnds(insn):
            for opnd in range(arities[insn]):
                yield get_var(ln_sort, f'insn_{insn}_opnd_{opnd}')

        def var_insn_opnds_val(insn, tys, instance):
            for opnd, ty in enumerate(tys):
                yield get_var(ty, f'insn_{insn}_opnd_{opnd}_{ty_name(ty)}_{instance}')

        def var_outs_val(instance):
            for opnd in var_insn_opnds_val(out_insn, out_tys, instance):
                yield opnd

        def var_insn_opnds_type(insn):
            for opnd in range(arities[insn]):
                yield get_var(ty_sort, f'insn_{insn}_opnd_type_{opnd}')

        def var_insn_res(insn, ty, instance):
            return get_var(ty, f'insn_{insn}_res_{ty_name(ty)}_{instance}')

        def var_insn_res_type(insn):
            return get_var(ty_sort, f'insn_{insn}_res_type')

        def var_input_res(insn, instance):
            return var_insn_res(insn, in_tys[insn], instance)

        def is_op_insn(insn):
            return insn >= n_inputs and insn < length - 1

        def add_constr_wfp(solver: Solver):
            # acyclic: line numbers of uses are lower than line number of definition
            # i.e.: we can only use results of preceding instructions
            for insn in range(length):
                for v in var_insn_opnds(insn):
                    solver.add(LE(v, insn - 1))

            # pin operands of an instruction that are not used (because of arity)
            # to the last input of that instruction
            for insn in range(n_inputs, length - 1):
                opnds = list(var_insn_opnds(insn))
                for op, op_id in self.op_enum.item_to_cons.items():
                    unused = opnds[op.arity:]
                    for opnd in unused:
                        solver.add(Implies(var_insn_op(insn) == op_id, \
                                           opnd == opnds[op.arity - 1]))

            # Add a constraint for the maximum amount of constants if specified.
            # The output instruction is exempt because we need to be able
            # to synthesize constant outputs correctly.
            max_const_ran = range(n_inputs, length - 1)
            if not max_const is None and len(max_const_ran) > 0:
                solver.add(LE(*[v for insn in max_const_ran \
                                for v in var_insn_opnds_is_const(insn)], max_const))  # AtMost replace by LE

            # if we have at most one type, we don't need type constraints
            if len(self.ty_enum) <= 1:
                return

            # for all instructions that get an op
            # add constraints that set the type of an instruction's operand
            # and the result type of an instruction
            types = self.ty_enum.item_to_cons
            for insn in range(n_inputs, length - 1):
                self.op_enum.add_range_constr(solver, var_insn_op(insn))
                for op, op_id in self.op_enum.item_to_cons.items():
                    # add constraints that set the result type of each instruction
                    solver.add(Implies(var_insn_op(insn) == op_id, \
                                       var_insn_res_type(insn) == types[op.out_type]))
                    # add constraints that set the type of each operand
                    for op_ty, v in zip(op.in_types, var_insn_opnds_type(insn)):
                        solver.add(Implies(var_insn_op(insn) == op_id, \
                                           v == types[op_ty]))

            # define types of inputs
            for inp, ty in enumerate(in_tys):
                solver.add(var_insn_res_type(inp) == types[ty])

            # define types of outputs
            for v, ty in zip(var_insn_opnds_type(out_insn), out_tys):
                solver.add(v == types[ty])

            # constrain types of outputs
            for insn in range(n_inputs, length):
                for other in range(0, insn):
                    for opnd, c, ty in zip(var_insn_opnds(insn), \
                                           var_insn_opnds_is_const(insn), \
                                           var_insn_opnds_type(insn)):
                        solver.add(Implies(Not(c), Implies(opnd == other, \
                                                           ty == var_insn_res_type(other))))
                self.ty_enum.add_range_constr(solver, var_insn_res_type(insn))

        def add_constr_opt(solver: Solver):
            def opnd_set(insn):
                ext = length - ln_sort.size()
                assert ext >= 0
                res = BV(0, length)
                one = BV(1, length)
                for opnd in var_insn_opnds(insn):
                    res |= one << BVZExt(opnd, ext)
                return res

            if opt_insn_order:
                for insn in range(n_inputs, out_insn - 1):
                    solver.add(BVULE(opnd_set(insn), opnd_set(insn + 1)))

            for insn in range(n_inputs, out_insn):
                op_var = var_insn_op(insn)
                for op, op_id in self.op_enum.item_to_cons.items():
                    # if operator is commutative, force the operands to be in ascending order
                    if opt_commutative and op.is_commutative:
                        opnds = list(var_insn_opnds(insn))
                        c = [BVULE(l, u) for l, u in zip(opnds[:op.arity - 1], opnds[1:])]
                        solver.add(Implies(op_var == op_id, And(c, ctx)))

                    # force that at least one operand is not-constant
                    # otherwise, the operation is not needed because it would be fully constant
                    if opt_const:
                        vars = [Not(v) for v in var_insn_opnds_is_const(insn)][:op.arity]
                        assert len(vars) > 0
                        solver.add(Implies(op_var == op_id, Or(vars, ctx)))

                # Computations must not be replicated: If an operation appears again
                # in the program, at least one of the operands must be different from
                # a previous occurrence of the same operation.
                if opt_no_cse:
                    for other in range(n_inputs, insn):
                        un_eq = [p != q for p, q in zip(var_insn_opnds(insn), var_insn_opnds(other))]
                        assert len(un_eq) > 0
                        solver.add(Implies(op_var == var_insn_op(other), Or(un_eq)))

            # no dead code: each produced value is used
            if opt_no_dead_code:
                for prod in range(n_inputs, length):
                    opnds = [prod == v for cons in range(prod + 1, length) for v in var_insn_opnds(cons)]
                    if len(opnds) > 0:
                        solver.add(Or(opnds))

        def iter_opnd_info(insn, tys, instance):
            return zip(tys, \
                       var_insn_opnds(insn), \
                       var_insn_opnds_val(insn, tys, instance), \
                       var_insn_opnds_is_const(insn), \
                       var_insn_op_opnds_const_val(insn, tys))

        def add_constr_conn(solver, insn, tys, instance):
            for ty, l, v, c, cv in iter_opnd_info(insn, tys, instance):
                # if the operand is a constant, its value is the constant value
                solver.add(Implies(c, v == cv))
                # else, for other each instruction preceding it ...
                for other in range(insn):
                    r = var_insn_res(other, ty, instance)
                    # ... the operand is equal to the result of the instruction
                    solver.add(Implies(Not(c), Implies(l == other, v == r)))

        def add_constr_instance(solver, instance):
            # for all instructions that get an op
            for insn in range(n_inputs, length - 1):
                # add constraints to select the proper operation
                op_var = var_insn_op(insn)
                for op, op_id in self.op_enum.item_to_cons.items():
                    res = var_insn_res(insn, op.out_type, instance)
                    opnds = list(var_insn_opnds_val(insn, op.in_types, instance))
                    [precond], [phi] = op.instantiate([res], opnds)
                    solver.add(Implies(op_var == op_id, And([precond, phi])))
                # connect values of operands to values of corresponding results
                for op in ops:
                    add_constr_conn(solver, insn, op.in_types, instance)
            # add connection constraints for output instruction
            add_constr_conn(solver, out_insn, out_tys, instance)

        def add_constr_io_sample(solver, instance, in_vals, out_vals):
            # add input value constraints
            assert len(in_vals) == n_inputs and len(out_vals) == n_outputs
            for inp, val in enumerate(in_vals):
                assert not val is None
                res = var_input_res(inp, instance)
                solver.add(res == val)
            for out, val in zip(var_outs_val(instance), out_vals):
                assert not val is None
                solver.add(out == val)

        def add_constr_io_spec(solver, instance, in_vals):
            # add input value constraints
            assert len(in_vals) == n_inputs
            assert all(not val is None for val in in_vals)
            for inp, val in enumerate(in_vals):
                solver.add(val == var_input_res(inp, instance))
            outs = [v for v in var_outs_val(instance)]
            preconds, phis = spec.instantiate(outs, in_vals)
            for pre, phi in zip(preconds, phis):
                solver.add(Implies(pre, phi))

        def add_constr_sol_for_verif(model):
            for insn in range(length):
                if is_op_insn(insn):
                    v = var_insn_op(insn)
                    verif.add(model[v] == v)
                    val = model.evaluate(v, model_completion=True)
                    op = self.op_enum.get_from_model_val(val)
                    tys = op.in_types
                else:
                    tys = out_tys

                # set connection values
                for _, opnd, v, c, cv in iter_opnd_info(insn, tys, 'verif'):
                    is_const = (model[c] == TRUE()) if not model[c] is None else False
                    verif.add(is_const == c)
                    if is_const:
                        verif.add(model[cv] == v)
                    else:
                        verif.add(model[opnd] == opnd)

        def add_constr_spec_verif():
            verif_outs = list(var_outs_val('verif'))
            assert len(verif_outs) == len(eval_outs)
            assert len(verif_outs) == len(spec.preconds)
            for inp, e in enumerate(eval_ins):
                verif.add(var_input_res(inp, 'verif') == e)
            for v, e in zip(verif_outs, eval_outs):
                verif.add(v == e)

        def create_prg(model):
            def prep_opnds(insn, tys):
                for _, opnd, v, c, cv in iter_opnd_info(insn, tys, 'verif'):
                    is_const = (model[c] == TRUE()) if not model[c] is None else False
                    yield (is_const, model[cv] if is_const else model[opnd].as_long())

            insns = []
            for insn in range(n_inputs, length - 1):
                val = model.evaluate(var_insn_op(insn), model_completion=True)
                op = self.op_enum.get_from_model_val(val)
                opnds = [v for v in prep_opnds(insn, op.in_types)]
                insns += [(op, opnds)]
            outputs = [v for v in prep_opnds(out_insn, out_tys)]
            input_names = [str(v) for v in spec.inputs]
            return Prg(input_names, insns, outputs)

        def write_smt2(solver, *args):
            if not output_prefix is None:
                filename = f'{output_prefix}_{"_".join(str(a) for a in args)}.smt2'
                with open(filename, 'w') as f:
                    print(solver.to_smt2(), file=f)

        # setup the synthesis solver
        if theory:
            synth_solver = Solver(logic=theory, ctx=ctx)
        else:
            synth_solver = Solver()
        synth = synth_solver
        add_constr_wfp(synth)
        add_constr_opt(synth)

        stats = []
        samples = init_samples if len(init_samples) > 0 else self.sample_n(1)
        assert len(samples) > 0, 'need at least 1 initial sample'
        use_output_samples = spec.is_deterministic and spec.is_total
        d(3, 'use output samples:', use_output_samples)

        i = 0
        while True:
            stat = {}
            stats += [stat]
            old_i = i

            for sample in samples:
                sample_str = str(sample)
                if len(sample_str := str(sample)) < 50:
                    sample_out = sample_str
                else:
                    sample_out = sample_str[:50] + '...'
                d(1, 'sample', i, sample_out)
                add_constr_instance(synth, i)
                if use_output_samples:
                    out_vals = self.eval_spec(sample)
                    add_constr_io_sample(synth, i, sample, out_vals)
                else:
                    add_constr_io_spec(synth, i, sample)
                i += 1

            samples_str = f'{i - old_i}' if i - old_i > 1 else old_i
            d(5, 'synth', samples_str, synth)
            write_smt2(synth, 'synth', n_insns, i)
            if reset_solver:
                synth_solver.reset()
                synth_solver.add(synth)
            with timer() as elapsed:
                res = synth_solver.check()
                synth_time = elapsed()
                d(3, synth_solver.statistics())
                d(2, f'synth time: {synth_time / 1e9:.3f}')
                stat['synth'] = synth_time

            if is_sat(res):
                # if sat, we found location variables
                m = synth_solver.model()
                prg = create_prg(m)
                stat['prg'] = str(prg).replace('\n', '; ')

                d(4, 'model: ', m)
                d(2, 'program:', stat['prg'])

                # push a new verification solver state
                verif.push()
                # Add constraints that represent the instructions of
                # the synthesized program
                add_constr_instance(verif, 'verif')
                # Add constraints that relate the specification to
                # the inputs and outputs of the synthesized program
                add_constr_spec_verif()
                # add constraints that set the location variables
                # in the verification constraint
                add_constr_sol_for_verif(m)

                d(5, 'verif', samples_str, verif)
                write_smt2(verif, 'verif', n_insns, samples_str)
                with timer() as elapsed:
                    res = verif.check()
                    verif_time = elapsed()
                stat['verif'] = verif_time
                d(2, f'verif time {verif_time / 1e9:.3f}')

                if is_sat(res):
                    # there is a counterexample, reiterate
                    samples = [_eval_model(self.verif, self.inputs)]
                    d(4, 'verification model', verif.model())
                    d(4, 'verif sample', samples[0])
                    verif.pop()
                else:
                    verif.pop()
                    # we found no counterexample, the program is therefore correct
                    d(1, 'no counter example found')
                    return prg, stats
            else:
                assert not is_sat(res)
                d(1, f'synthesis failed for size {n_insns}')
                return None, stats


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
    push_env()
    spec_solver = SpecWithSolver(spec, ops)
    init_samples = spec_solver.sample_n(n_samples)
    for n_insns in iter_range:
        with timer() as elapsed:
            prg, stats = spec_solver.synth_n(n_insns, \
                                             init_samples=init_samples, **args)
            all_stats += [{'time': elapsed(), 'iterations': stats}]
            if not prg is None:
                return prg, all_stats
    return None, all_stats


class Bl:
    w, x, y, z = Symbol('w'), Symbol('x'), Symbol('y'), Symbol('z')
    i2 = [x, y]
    i3 = i2 + [z]
    i4 = [w] + i3
    not1 = Func('not', Not(x))  # 7404
    nand2 = Func('nand2', Not(And(i2)))  # 7400
    nor2 = Func('nor2', Not(Or(i2)))  # 7402
    and2 = Func('and2', And(i2))  # 7408
    or2 = Func('or2', Or(i2))  # 7432
    xor2 = Func('xor2', Xor(x, y))  # 7486

    and3 = Func('and3', And(i3))  # 7408
    or3 = Func('or3', Or(i3))  # 7432

    nand3 = Func('nand3', Not(And(i3)))  # 7410
    nor3 = Func('nor3', Not(Or(i3)))  # 7427
    and3 = Func('and3', And(i3))  # 7411

    nand4 = Func('nand4', Not(And(i4)))  # 7420
    and4 = Func('and4', And(i4))  # 7421
    nor4 = Func('nor4', Not(Or(i4)))  # 7429

    mux2 = Func('mux2', Or(And(w, x), And(Not(w), y)))
    maj3 = Func('maj3', Or(And(x, y), And(x, z), And(y, z)))
    eq2 = Func('eq2', EqualsOrIff(x, y))


class Bv:
    def __init__(self, width):
        self.width = width
        self.ty = BVType(width)

        x = Symbol('x', BVType())
        y = Symbol('y', BVType())
        shift_precond = And([y >= 0, y < width])
        div_precond = y != 0
        z = BV(0, width)
        o = BV(1, width)

        l = [
            Func('neg', -x),
            Func('not', ~x),
            Func('and', x & y),
            Func('or', x | y),
            Func('xor', x ^ y),
            Func('add', x + y),
            Func('sub', x - y),
            Func('mul', x * y),
            Func('div', x / y),
            Func('udiv', BVUDiv(x, y), precond=div_precond),
            Func('smod', x % y, precond=div_precond),
            Func('urem', BVURem(x, y), precond=div_precond),
            Func('srem', BVSRem(x, y), precond=div_precond),
            Func('shl', (x << y), precond=shift_precond),
            Func('lshr', BVLShr(x, y), precond=shift_precond),
            Func('ashr', x >> y, precond=shift_precond),
            Func('uge', Ite(BVUGE(x, y), o, z)),
            Func('ult', Ite(BVULT(x, y), o, z)),
            Func('sge', Ite(x >= y, o, z)),
            Func('slt', Ite(x < y, o, z)),
        ]

        for op in l:
            setattr(self, f'{op.name}_', op)


def create_random_formula(inputs, size, ops, seed=0x5aab199e):
    random.seed(a=seed, version=2)
    assert size > 0

    def create(size):
        nonlocal inputs, ops, seed
        assert size > 0
        if size == 1:
            return random.choice(inputs)
        elif size == 2:
            op = random.choice([op for op, n in ops if n == 1])
            return op(create(1))
        else:
            size -= 1
            op, arity = random.choice(ops)
            assert arity <= 2
            if arity == 1:
                return op(create(size))
            else:
                assert arity == 2
                szl = random.choice(range(size - 1)) + 1
                szr = size - szl
                return op(create(szl), create(szr))

    return create(size)


def create_random_dnf(inputs, clause_probability=50, seed=0x5aab199e):
    """Creates a random DNF formula.

    Attributes:
    inputs: List of Z3 variables that determine the number of variables in the formula.
    clause_probability: Probability of a clause being added to the formula.
    seed: Seed for the random number generator.

    This function iterates over *all* clauses, and picks based on the
    clause_probability if a clause is added to the formula.
    Therefore, the function's running time is exponential in the number of variables.
    """
    # sample function results
    random.seed(a=seed, version=2)
    clauses = []
    for vals in itertools.product(*[range(2)] * len(inputs)):
        if random.choice(range(100)) < clause_probability:
            clauses += [And([inp if pos else Not(inp) for inp, pos in zip(inputs, vals)])]
    return Or(clauses)


def create_bool_func(func):
    def is_power_of_two(x):
        return (x & (x - 1)) == 0

    if re.match('^0[bodx]', func):
        base = {'b': 2, 'o': 8, 'd': 10, 'x': 16}[func[1]]
        func = func[2:]
    else:
        base = 16
    assert is_power_of_two(base), 'base of the number must be power of two'
    bits_per_digit = int(math.log2(base))
    n_bits = len(func) * bits_per_digit
    bits = bin(int(func, base))[2:].zfill(n_bits)
    assert len(bits) == n_bits
    assert is_power_of_two(n_bits), 'length of function must be power of two'
    n_vars = int(math.log2(n_bits))
    vars = [Bool(f'x{i}') for i in range(n_vars)]
    clauses = []
    binary = lambda i: bin(i)[2:].zfill(n_vars)
    for i, bit in enumerate(bits):
        if bit == '1':
            clauses += [And([vars[j] if b == '1' else Not(vars[j]) \
                             for j, b in enumerate(binary(i))])]
    return Func(func, Or(clauses) if len(clauses) > 0 else And(vars[0], Not(vars[0])))


class TestBase:
    def __init__(self, maxlen=10, debug=0, stats=False, graph=False, tests=None, write=None):
        self.debug = debug
        self.max_length = maxlen
        self.write_stats = stats
        self.write_graph = graph
        self.tests = tests
        self.write = write

    def do_synth(self, name, spec, ops, desc='', **args):
        desc = f' ({desc})' if len(desc) > 0 else ''
        print(f'{name}{desc}: ', end='', flush=True)
        output_prefix = name if self.write else None
        prg, stats = synth(spec, ops, range(self.max_length), \
                           debug=self.debug, output_prefix=output_prefix, **args)
        total_time = sum(s['time'] for s in stats)
        print(f'{total_time / 1e9:.3f}s')
        if self.write_stats:
            with open(f'{name}.json', 'w') as f:
                json.dump(stats, f, indent=4)
        if self.write_graph:
            with open(f'{name}.dot', 'w') as f:
                prg.print_graphviz(f)
        print(prg)
        return total_time

    def run(self):
        # iterate over all methods in this class that start with 'test_'
        if self.tests is None:
            tests = [name for name in dir(self) if name.startswith('test_')]
        else:
            tests = ['test_' + s for s in self.tests.split(',')]
        tests.sort()
        total_time = 0
        for name in tests:
            push_env()
            total_time += getattr(self, name)()
            print('')
        print(f'total time: {total_time / 1e9:.3f}s')


# I only need a function with 3 params currently, since n is always 2
def at_least(x, y, z, n=2):
    if n == 2:
        return Or(And(x, y), And(x, z), And(y, z))
    else:
        raise NotImplementedError


class Tests(TestBase):

    def random_test(self, name, n_vars, create_formula):
        ops = [Bl.and2, Bl.or2, Bl.xor2, Bl.not1]
        spec = Func('rand', create_formula([Symbol(f'x{i}') for i in range(n_vars)]))
        return self.do_synth(name, spec, ops, max_const=0, theory='QF_FD')

    def test_rand(self, size=40, n_vars=4):
        ops = [(And, 2), (Or, 2), (Xor, 2), (Not, 1)]
        f = lambda x: create_random_formula(x, size, ops)
        return self.random_test('rand_formula', n_vars, f)

    def test_rand_dnf(self, n_vars=4):
        f = lambda x: create_random_dnf(x)
        return self.random_test('rand_dnf', n_vars, f)

    def test_npn4_1789(self):
        ops = [Bl.and2, Bl.or2, Bl.xor2, Bl.not1]
        name = '1789'
        spec = create_bool_func(name)
        return self.do_synth(f'npn4_{name}', spec, ops, max_const=0, n_samples=16, \
                             reset_solver=True, theory='QF_FD')

    def test_and(self):
        return self.do_synth('and', Bl.and2, [Bl.and2])

    def test_xor(self):
        ops = [Bl.nand2]
        return self.do_synth('xor', Bl.xor2, ops)

    def test_mux(self):
        return self.do_synth('mux', Bl.mux2, [Bl.and2, Bl.xor2])

    def test_zero(self):
        spec = Func('zero', Not(Or([Bool(f'x{i}') for i in range(8)])))
        ops = [Bl.and2, Bl.nand2, Bl.or2, Bl.nor2, Bl.nand3, Bl.nor3, Bl.nand4, Bl.nor4]
        return self.do_synth('zero', spec, ops, max_const=0, theory='QF_FD')

    def test_add(self):
        x = Symbol('x', INT)
        y = Symbol('y', INT)
        ci = Symbol('ci', INT)
        s = Symbol('s', INT)
        co = Symbol('co', INT)
        add = [co == at_least(x, y, ci, 2), s == Xor(x, Xor(y, ci))]
        spec = Spec('adder', add, [s, co], [x, y, ci])
        ops = [Bl.and2, Bl.or2, Bl.xor2, Bl.not1]
        return self.do_synth('add', spec, ops, desc='1-bit full adder', \
                             theory='QF_FD')

    def test_add_apollo(self):
        x = Symbol('x')
        y = Symbol('y')
        s = Symbol('ci')
        ci = Symbol('s')
        co = Symbol('co')
        add = [co == at_least(x, y, ci, 2), s == Xor(x, Xor(y, ci))]
        spec = Spec('adder', add, [s, co], [x, y, ci])
        return self.do_synth('add_nor3', spec, [Bl.nor3], \
                             desc='1-bit full adder (nor3)', theory='QF_FD')

    def test_identity(self):
        spec = Func('magic', And(Or(Bool('x'))))
        ops = [Bl.nand2, Bl.nor2, Bl.and2, Bl.or2, Bl.xor2]
        return self.do_synth('identity', spec, ops)

    def test_true(self):
        x = Symbol('x')
        y = Symbol('y')
        z = Symbol('z')
        spec = Func('magic', Or(Or(x, y, z), Not(x)))
        ops = [Bl.nand2, Bl.nor2, Bl.and2, Bl.or2, Bl.xor2]
        return self.do_synth('true', spec, ops, desc='constant true')

    def test_false(self):
        x = Symbol('x')
        y = Symbol('y')
        z = Symbol('z')
        spec = Spec('magic', [z == Or([])], [z], [x])
        ops = [Bl.nand2, Bl.nor2, Bl.and2, Bl.or2, Bl.xor2]
        return self.do_synth('false', spec, ops, desc='constant false')

    def test_multiple_types(self):
        x = Symbol('x', INT)
        y = Symbol('y', BVType())
        int2bv = Func('int2bv', BV(x, 16))
        bv2int = Func('bv2int', BVToNatural(y))
        div2 = Func('div2', x / 2)
        spec = Func('shr2', BVLShr((BVZExt(y, 8), 1)))
        ops = [int2bv, bv2int, div2]
        return self.do_synth('multiple_types', spec, ops)

    def test_precond(self):
        x = Symbol('x', INT)
        b = Symbol('b', BVType())
        int2bv = Func('int2bv', BV(x, 8))
        bv2int = Func('bv2int', BVToNatural(b))
        mul2 = Func('addadd', b + b)
        spec = Func('mul2', x * 2, And([x >= 0, x < 128]))
        ops = [int2bv, bv2int, mul2]
        return self.do_synth('preconditions', spec, ops)

    def test_constant(self):
        x = Symbol('x', INT)
        y = Symbol('y', INT)
        mul = Func('mul', x * y)
        spec = Func('const', x + x)
        return self.do_synth('constant', spec, [mul])

    def test_abs(self):
        w = 32
        x = Symbol('x', BVType(w))
        y = Symbol('y', BVType(w))
        ops = [
            Func('sub', Minus(x, y)),
            Func('xor', Xor(x, y)),
            Func('shr', x >> y, precond=And([y >= 0, y < w]))
        ]
        spec = Func('spec', Ite(x >= 0, x, -x))
        return self.do_synth('abs', spec, ops, theory='QF_FD')

    def test_pow(self):
        x = Symbol('x', INT)
        y = Symbol('y', INT)
        expr = x
        for _ in range(30):
            expr = expr * x
        spec = Func('pow', expr)
        ops = [Func('mul', x * y)]
        return self.do_synth('pow', spec, ops, max_const=0)

    def test_poly(self):
        a = Symbol('a', INT)
        b = Symbol('b', INT)
        c = Symbol('c', INT)
        h = Symbol('h', INT)
        spec = Func('poly', a * h * h + b * h + c)
        ops = [Func('mul', a * b), Func('add', a + b)]
        return self.do_synth('poly', spec, ops, max_const=0)

    def test_array(self):
        def Arr(name):
            return Array(name, PySMTType(), PySMTType())  # TODO Compare z3 and pysmt Array functions

        def permutation(array, perm):
            res = array
            for fr, to in enumerate(perm):
                if fr != to:
                    res = Store(res, to, Select(array, fr))
            return res

        def swap(a, x, y):
            b = Store(a, x, Select(a, y))
            c = Store(b, y, Select(a, x))
            return c

        x = Array('x', PySMTType(), PySMTType())
        p = Symbol('p', INT)
        op = Func('swap', swap(x, p, p + 1))
        spec = Func('rev', permutation(x, [3, 2, 1, 0]))
        return self.do_synth('array', spec, [op])


def parse_standard_args():
    import argparse
    parser = argparse.ArgumentParser(prog="synth")
    parser.add_argument('-d', '--debug', type=int, default=0)
    parser.add_argument('-m', '--maxlen', type=int, default=10)
    parser.add_argument('-s', '--stats', default=False, action='store_true')
    parser.add_argument('-g', '--graph', default=False, action='store_true')
    parser.add_argument('-w', '--write', default=False, action='store_true')
    parser.add_argument('-t', '--tests', default=None, type=str)
    return parser.parse_args()


# Enable Z3 parallel mode
# set_param("parallel.enable", True)
# TODO Check for parallel mode in pysmt

if __name__ == "__main__":
    args = parse_standard_args()
    tests = Tests(**vars(args))
    tests.run()
