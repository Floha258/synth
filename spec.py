from functools import cached_property
from itertools import combinations as comb, permutations as perm

from z3 import Z3_OP_UNINTERPRETED, ExprRef, BoolRef, BoolVal, Solver, Not, unsat, FreshConst, And, Or, substitute, \
    Const, Context

import smtlib
from smtlib import solve_smtlib, SupportedSolvers, _eval_model


def write_smt2(filename: str, solver):
    s = solver
    if not type(s) is Solver:
        s = Solver()  # TODO Might need to add ctx back to solver (Solver(ctx=ctx))
        s.add(solver)
    if filename:
        with open(filename, 'w') as f:
            print(s.to_smt2(), file=f)
            print('(get-model)', file=f)

class Spec:
    def collect_vars(expr):
        res = set()
        def collect(expr):
            if len(expr.children()) == 0 and expr.decl().kind() == Z3_OP_UNINTERPRETED:
                res.add(expr)
            else:
                for c in expr.children():
                    collect(c)
        collect(expr)
        return res

    def __init__(self, name: str, phi: ExprRef, outputs: list[ExprRef], \
                 inputs: list[ExprRef], precond: BoolRef = None):
        """
        Create a specification.

        A specification object represents n specifications each given
        by a Z3 expression (phi).

        inputs is the list of input variables that the n formulas use.
        outputs is the list of output variables that the n formulas use.
        There must be as many variables in outputs as there are formulas in phi.
        Each specification can optionally have a precondition (preconds)
        to express partial functions.
        If preconds is None, all preconditions are True.

        Specifications can be non-deterministic.

        Attributes:
        name: Name of the specification.
        phi: Z3 expression that represents the specification
        outputs: List of output variables in phi.
        inputs: List of input variables in phi.
        precond: A precondition for the specification
            (if None, the precondition is True).

        Note that the names of the variables don't matter because when
        used in the synthesis process their names are substituted by internal names.
        """
        self.ctx      = phi.ctx
        self.name     = name
        self.arity    = len(inputs)
        self.inputs   = inputs
        self.outputs  = outputs
        self.phi      = phi
        self.precond  = BoolVal(True, ctx=self.ctx) if precond is None else precond
        self.vars     = Spec.collect_vars(phi)
        all_vars      = outputs + inputs
        assert len(set(all_vars)) == len(all_vars), 'outputs and inputs must be unique'
        assert self.vars <= set(all_vars), \
            f'phi must use only out and in variables: {self.vars} vs {all_vars}'
        assert Spec.collect_vars(self.precond) <= set(self.inputs), \
            f'precondition must use input variables only'
        assert Spec.collect_vars(self.phi) <= set(inputs + outputs), \
            f'i-th spec must use only i-th out and input variables {phi}'

    def __str__(self):
        return self.name

    def translate(self, ctx):
        ins  = [ x.translate(ctx) for x in self.inputs ]
        outs = [ x.translate(ctx) for x in self.outputs ]
        pre  = self.precond.translate(ctx)
        phi  = self.phi.translate(ctx)
        return Spec(self.name, phi, outs, ins, pre)

    @cached_property
    def eval(self):
        s = Solver(ctx=self.ctx)
        s.add(self.precond)
        s.add(self.phi)
        return Eval(self.inputs, self.outputs, s, self.name)

    @cached_property
    def out_types(self):
        return [ v.sort() for v in self.outputs ]

    @cached_property
    def in_types(self):
        return [ v.sort() for v in self.inputs ]

    @cached_property
    def is_total(self):
        solver = Solver(ctx=self.ctx)
        solver.add(Not(self.precond))
        filename = f'total_{self.name}.smt2'
        write_smt2(filename, solver)
        return not smtlib.solve_smtlib(filename, SupportedSolvers.CVC)[0]

    @cached_property
    def is_deterministic(self):
        solver  = Solver(ctx=self.ctx)
        ins     = [ FreshConst(ty) for ty in self.in_types ]
        outs    = [ FreshConst(ty) for ty in self.out_types ]
        _, phi  = self.instantiate(outs, ins)
        solver.add(self.precond)
        solver.add(self.phi)
        solver.add(phi)
        solver.add(And([a == b for a, b in zip(self.inputs, ins)]))
        solver.add(Or ([a != b for a, b in zip(self.outputs, outs)]))
        filename = f'deterministic_{self.name}.smt2'
        write_smt2(filename, solver)
        return not smtlib.solve_smtlib(filename, SupportedSolvers.CVC)[0]

    def instantiate(self, outs, ins):
        self_outs = self.outputs
        self_ins  = self.inputs
        assert len(outs) == len(self_outs)
        assert len(ins) == len(self_ins)
        assert all(x.ctx == y.ctx for x, y in zip(self_outs + self_ins, outs + ins))
        phi = substitute(self.phi, list(zip(self_outs + self_ins, outs + ins)))
        pre = substitute(self.precond, list(zip(self_ins, ins)))
        return pre, phi


class Func(Spec):
    def __init__(self, name, phi, precond=BoolVal(True), inputs=[]):
        """Creates an Op from a Z3 expression.

        Attributes:
        name: Name of the operator.
        phi: Z3 expression that represents the semantics of the operator.
        precond: Z3 expression that represents the precondition of the operator.
        inputs: List of input variables in phi. If [] is given, the inputs
            are taken in lexicographical order.
        """
        input_vars = Spec.collect_vars(phi)
        # if no inputs are specified, we take the identifiers in
        # lexicographical order. That's just a convenience
        if len(inputs) == 0:
            inputs = sorted(input_vars, key=lambda v: str(v))
        # create Z3 variable of a given sort
        input_names = set(str(v) for v in inputs)
        names = [ n for n in 'yzr' if not n in input_names ]
        res_ty = phi.sort()
        self.func = phi
        out = Const(names[0], res_ty) if names else FreshConst(res_ty, 'y')
        super().__init__(name, out == phi, [ out ], inputs, precond=precond)

    @cached_property
    def out_type(self):
        return self.out_types[0]

    def translate(self, ctx):
        ins = [ i.translate(ctx) for i in self.inputs ]
        return Func(self.name, \
                    self.func.translate(ctx), \
                    self.precond.translate(ctx), ins)

    @cached_property
    def is_deterministic(self):
        return True

    @cached_property
    def is_commutative(self):
        # if the operator inputs have different sorts, it cannot be commutative
        if len(set(v.sort() for v in self.inputs)) > 1 or len(self.inputs) > 3:
            return False
        ctx     = Context()
        precond = self.precond.translate(ctx)
        func    = self.func.translate(ctx)
        ins     = [ x.translate(ctx) for x in self.inputs ]
        subst   = lambda f, i: substitute(f, list(zip(ins, i)))
        fs = [ And([ subst(precond, a), subst(precond, b), \
                     subst(func, a) != subst(func, b) ], ctx) \
                for a, b in comb(perm(ins), 2) ]
        s = Solver(ctx=ctx)
        s.add(Or(fs, ctx))

        filename = f'commutative_{self.name}.smt2'
        write_smt2(filename, s)
        return not smtlib.solve_smtlib(filename, SupportedSolvers.CVC)[0]


class Eval:
    def __init__(self, inputs, outputs, solver, name):
        self.inputs = inputs
        self.outputs = outputs
        self.solver = solver
        self.name = name



    def __call__(self, input_vals):
        s = self.solver
        s.push()
        for var, val in zip(self.inputs, input_vals):
            s.add(var == val)
        # assert s.check() == sat
        filename = f'{self.name}_eval_{"_".join(str(i) for i in self.inputs)}.smt2'
        write_smt2(filename, self.solver)
        solvable, _, model = solve_smtlib(filename, SupportedSolvers.CVC)
        assert solvable
        res = _eval_model(model, self.outputs)
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
        for i in range(n):
            filename = f'{self.name}_sample_{i}.smt2'
            write_smt2(filename, s)
            solvable, _, model = solve_smtlib(filename, SupportedSolvers.CVC)
            if solvable:
                ins  = _eval_model(model, self.inputs)
                res += [ ins ]
                s.add(Or([ v != iv for v, iv in zip(self.inputs, ins) ]))
            else:
                assert len(res) > 0, 'cannot evaluate'
        s.pop()
        return res
