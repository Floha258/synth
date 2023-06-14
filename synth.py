#! /usr/bin/env python3

import random
import itertools
import time
import json
import inspect

from itertools import combinations as comb
from itertools import permutations as perm

from z3 import *

class Op:
    def __init__(self, name: str, opnd_tys: list, res_ty, formula, \
                 precond=lambda x: True):
        """Create an op.

        Attributes:
        name: Name of the op.
        opnd_tys: List of operand types.
            An operand type is a Z3 type constructor such as Bool or Int.
        res_ty: Result type.
        formula: A function that takes a list of operands (whose type match
            the types in opnd_tys) and returns a Z3 expression whose
            type is res_ty.
        precond: A function that takes a list of operands (like formula)
            and returns a Z3 expression that represents the precondition.
            Its result has to be a Bool.

        Note that the types need to be functions that take a string and
        give a Z3 variable (such as the functions Bool or Int).
        They cannot be lambdas because we use their __name__ attribute
        to create unique variable names.
        """
        self.name     = name
        self.phi      = formula
        self.precond  = precond
        self.opnd_tys = opnd_tys
        self.res_ty   = res_ty
        self.arity    = len(self.opnd_tys)
        self.comm     = False if self.arity < 2 or len(set(opnd_tys)) > 1 else None

    def __str__(self):
        return self.name

    def is_const(self):
        return False

    def is_commutative(self):
        if self.comm is None:
            ins = [ ty(f'{self.name}_in_comm_{i}') for i, ty in enumerate(self.opnd_tys) ]
            fs = [ Implies(And([self.precond(a), self.precond(b)]), self.phi(a) != self.phi(b)) \
                    for a, b in comb(perm(ins), 2) ]
            s = Solver()
            s.add(Or(fs))
            self.comm = s.check() == unsat
        return self.comm

class Prg:
    def __init__(self, input_names, insns, outputs):
        """Creates a program.

        Attributes:
        input_names: list of names of the inputs
        insns: List of instructions.
            This is a list of triples where each triple consists
            of an Op, an optional attribute, and a list of integers
            where each integer indicates the variable number of the operand.
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
        jv   = lambda args: ', '.join(str(v) if c else self.var_name(v) for c, v in args)
        res = ''.join(f'{self.var_name(i + n_inputs)} = {op.name}({jv(args)})\n' \
                      for i, (op, args) in enumerate(self.insns))
        return res + f'return({jv(self.outputs)})'

def ty_name(ty):
    return ty.__name__ if inspect.isfunction(ty) else str(ty)

def take_time(func, *args):
    start = time.perf_counter_ns()
    res = func(*args)
    return res, time.perf_counter_ns() - start

def synth(funcs: list[Op], ops: list[Op], to_len, from_len = 0, input_names=[], debug=0):
    """Synthesize a program that computes the given functions.

    Attributes:
    funcs: List of functions that the program has to compute.
        All functions have to have the same number of operands and
        have to agree on their operand types.
    ops: List of operations that can be used in the program.
    to_len: Maximum length of the program.
    from_len: Minimum length of the program.
    input_names: List of names of the inputs.
        If empty, default names are used.
    debug: Debug level. 0: no debug output, >0 more debug output.

    Returns:
    A tuple (prg, stats) where prg is the synthesized program and stats
    is a list of statistics for each iteration of the synthesis loop.
    """
    vars = {}
    # get types of input operands.
    # all functions need to agree on this.
    assert len(funcs) > 0
    in_tys = funcs[0].opnd_tys
    for s in funcs[1:]:
        assert in_tys == s.opnd_tys
    n_inputs = len(in_tys)

    # add default names for input variables if missing
    for i in range(len(input_names), n_inputs):
        input_names += [ f'i{i}' for i in range(n_inputs) ]

    # create map of types to their id
    n_types = 0
    types = {}
    for op in ops:
        for ty in op.opnd_tys + [ op.res_ty ]:
            if not ty in types:
                types[ty] = n_types
                n_types += 1

    max_arity = max(op.arity for op in ops)
    out_tys = [ op.res_ty for op in funcs ]
    out_insn = 0
    length = 0
    arities = []

    def d(*args):
        if debug > 0:
            print(*args)

    def dd(*args):
        if debug > 1:
            print(*args)

    def ddd(*args):
        if debug > 2:
            print(*args)

    def eval_spec(input_vals):
        """Evaluates the specification on the given inputs.
           The list has to be of length n_inputs.
           If you want to not set an input, use None.
        """
        assert len(input_vals) == n_inputs
        verif.push()
        for i, (v, e) in enumerate(zip(input_vals, eval_ins)):
            if not v is None:
                verif.add(e == v)
        res = verif.check()
        assert res == sat, 'specification is unsatisfiable'
        m = verif.model()
        verif.pop()
        return [ m[v] for v in eval_ins ], [ m[v] for v in eval_outs ]

    def get_var(ty, name):
        if name in vars:
            v = vars[name]
        else:
            assert ty
            v = ty(name)
            vars[name] = v
        return v

    def var_insn_op(insn):
        return get_var(Int, f'insn_{insn}_op')

    def var_insn_opnds_is_const(insn):
        for opnd in range(arities[insn]):
            yield get_var(Bool, f'insn_{insn}_opnd_{opnd}_is_const')

    def var_insn_op_opnds_const_val(insn, opnd_tys):
        for opnd, ty in enumerate(opnd_tys):
            yield get_var(ty, f'insn_{insn}_opnd_{opnd}_{ty_name(ty)}_const_val')

    def var_insn_opnds(insn):
        for opnd in range(arities[insn]):
            yield get_var(Int, f'insn_{insn}_opnd_{opnd}')

    def var_insn_opnds_val(insn, tys, instance):
        for opnd, ty in enumerate(tys):
            yield get_var(ty, f'insn_{insn}_opnd_{opnd}_{ty_name(ty)}_{instance}')

    def var_outs_val(instance):
        for opnd in var_insn_opnds_val(out_insn, out_tys, instance):
            yield opnd

    def var_insn_opnds_type(insn):
        for opnd in range(arities[insn]):
            yield get_var(Int, f'insn_{insn}_opnd_type_{opnd}')

    def var_insn_res(insn, ty, instance):
        return get_var(ty, f'insn_{insn}_res_{ty_name(ty)}_{instance}')

    def var_insn_res_type(insn):
        return get_var(Int, f'insn_{insn}_res_type')

    def var_input_res(insn, instance):
        return var_insn_res(insn, in_tys[insn], instance)

    def is_op_insn(insn):
        return insn >= n_inputs and insn < length - 1

    def add_constr_wfp(solver: Solver):
        # acyclic: line numbers of uses are lower than line number of definition
        # i.e.: we can only use results of preceding instructions
        for insn in range(length):
            for v in var_insn_opnds(insn):
                solver.add(0 <= v)
                solver.add(v < insn)

        # for all instructions that get an op
        # add constraints that set the type of an instruction's operands and result type
        for insn in range(n_inputs, length - 1):
            for op_id, op in enumerate(ops):
                # add constraints that set the result type of each instruction
                solver.add(Implies(var_insn_op(insn) == op_id, \
                                   var_insn_res_type(insn) == types[op.res_ty]))
                # add constraints that set the type of each operand
                for op_ty, v in zip(op.opnd_tys, var_insn_opnds_type(insn)):
                    solver.add(Implies(var_insn_op(insn) == op_id, v == types[op_ty]))

            # constrain the op variable to the number of ops
            o = var_insn_op(insn)
            solver.add(0 <= o)
            solver.add(o < len(ops))

        # define types of inputs
        for inp, ty in enumerate(in_tys):
            solver.add(var_insn_res_type(inp) == types[ty])

        # define types of outputs
        for v, ty in zip(var_insn_opnds_type(out_insn), out_tys):
            solver.add(v == types[ty])

        # constrain types of outputs
        for insn in range(n_inputs, length):
            for other in range(0, insn):
                for opnd, ty in zip(var_insn_opnds(insn), \
                                    var_insn_opnds_type(insn)):
                    solver.add(Implies(opnd == other, ty == var_insn_res_type(other)))

    def add_constr_opt(solver: Solver):
        # if operator is commutative, the operands can be linearly ordered
        for insn in range(n_inputs, length - 1):
            op_var = var_insn_op(insn)
            for op_id, op in enumerate(ops):
                if op.is_commutative():
                    opnds = list(var_insn_opnds(insn))
                    c = [ l <= u for l, u in zip(opnds[:op.arity - 1], opnds[1:]) ]
                    solver.add(Implies(op_var == op_id, And(c)))

        # Computations must not be replicated: If an operation appears again
        # in the program, at least one of the operands must be different from
        # a previous occurrence of the same operation.
        for insn in range(n_inputs, length - 1):
            for other in range(n_inputs, insn):
                un_eq = [ p != q for p, q in zip(var_insn_opnds(insn), var_insn_opnds(other)) ]
                solver.add(Implies(var_insn_op(insn) == var_insn_op(other), Or(un_eq)))

        # add constraints that says that each produced value is used
        for prod in range(n_inputs, length):
            opnds = [ prod == v for cons in range(prod + 1, length) for v in var_insn_opnds(cons) ]
            if len(opnds) > 0:
                solver.add(Or(opnds))

        # not all operands of an operator can be constant
        for insn in range(n_inputs, length - 1):
            solver.add(Or([ Not(v) for v in var_insn_opnds_is_const(insn) ]))

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
            for op_id, op in enumerate(ops):
                res = var_insn_res(insn, op.res_ty, instance)
                opnds = list(var_insn_opnds_val(insn, op.opnd_tys, instance))
                solver.add(Implies(op_var == op_id, op.precond(opnds)))
                solver.add(Implies(op_var == op_id, res == op.phi(opnds)))
            # connect values of operands to values of corresponding results
            for op in ops:
                add_constr_conn(solver, insn, op.opnd_tys, instance)
        # add connection constraints for output instruction
        add_constr_conn(solver, out_insn, out_tys, instance)

    def add_constr_io_sample(solver, instance, io_sample):
        # add input value constraints
        in_vals, out_vals = io_sample
        assert len(in_vals) == n_inputs and len(out_vals) == len(funcs)
        for inp, val in enumerate(in_vals):
            if not val is None:
                res = var_input_res(inp, instance)
                solver.add(res == val)
        for out, val in zip(var_outs_val(instance), out_vals):
            if not val is None:
                solver.add(out == val)

    def add_constr_sol_for_verif(model):
        for insn in range(length):
            if is_op_insn(insn):
                v = var_insn_op(insn)
                verif.add(model[v] == v)
                op = model[v].as_long()
                tys = ops[op].opnd_tys
            else:
                tys = out_tys

            # set connection values
            for _, opnd, v, c, cv in iter_opnd_info(insn, tys, 'verif'):
                is_const = is_true(model[c]) if not model[c] is None else False
                verif.add(is_const == c)
                if is_const:
                    verif.add(model[cv] == v)
                else:
                    verif.add(model[opnd] == opnd)

    def add_constr_spec_verif():
        for inp, e in enumerate(eval_ins):
            verif.add(var_input_res(inp, 'verif') == e)
        verif.add(Or([v != e for v, e in zip(var_outs_val('verif'), eval_outs)]))

    def create_prg(model):
        def prep_opnds(insn, tys):
            for _, opnd, v, c, cv in iter_opnd_info(insn, tys, 'verif'):
                is_const = is_true(model[c])
                yield (is_const, model[cv] if is_const else model[opnd].as_long())

        insns = []
        for insn in range(n_inputs, length - 1):
            op     = ops[model[var_insn_op(insn)].as_long()]
            # opnds  = [ model[v].as_long() for v in var_insn_opnds(insn) ][:op.arity]
            opnds  = [ v for v in prep_opnds(insn, op.opnd_tys) ]#[:op.arity]
            insns += [ (op, opnds) ]
        outputs = [ v for v in prep_opnds(out_insn, out_tys) ]
        return Prg(input_names, insns, outputs)

    # create the verification solver.
    # For now, it is just able to sample the specification
    verif = Solver()
    # all result variables of the inputs
    eval_ins = [ get_var(ty, f'eval_in_{i}') for i, ty in enumerate(in_tys) ]
    # the operand value variables of the output instruction
    eval_outs = [ get_var(ty, f'eval_out_{i}') for i, ty in enumerate(out_tys) ]
    for o, s in zip(eval_outs, funcs):
        verif.add(s.precond(eval_ins))
        verif.add(o == s.phi(eval_ins))

    def synth_len(n_insns):
        nonlocal out_insn, length, arities
        out_insn = len(in_tys) + n_insns
        length   = out_insn + 1
        arities  = [ 0 ] * n_inputs + [ max_arity ] * n_insns + [ len(funcs) ]

        d('size', n_insns)

        # get the synthesis solver
        synth = Then('simplify', 'solve-eqs', 'smt').solver()

        # setup the synthesis constraint
        add_constr_wfp(synth)
        add_constr_opt(synth)

        stats = []
        # sample the specification once for an initial set of input samples
        sample = eval_spec([None] * n_inputs)
        i = 0
        while True:
            stat = {}
            stats += [ stat ]

            d('sample', i)
            dd(sample)
            add_constr_instance(synth, i)
            add_constr_io_sample(synth, i, sample)

            ddd('synth', i, synth)
            res, stat['synth'] = take_time(synth.check)

            if res == sat:
                # if sat, we found location variables
                m = synth.model()
                prg = create_prg(m)
                stat['prg'] = str(prg).replace('\n', '; ')

                dd('model: ', m)
                dd('program: ', prg)

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

                ddd('verif', i, verif)
                res, stat['verif'] = take_time(verif.check)

                if res == sat:
                    # there is a counterexample, reiterate
                    m = verif.model()
                    ddd('verification model', m)
                    verif.pop()
                    sample = eval_spec([ m[e] for e in eval_ins ])
                    i += 1
                else:
                    # clean up the verification solver state
                    verif.pop()
                    # we found no counterexample, the program is therefore correct
                    d('no counter example found')
                    return prg, stats
            else:
                assert res == unsat
                d(f'synthesis failed for size {n_insns}')
                return None, stats

    all_stats = []
    for n_insns in range(from_len, to_len + 1):
        (prg, stats), t = take_time(synth_len, n_insns)
        all_stats += [ { 'time': t, 'iterations': stats } ]
        if not prg is None:
            return prg, all_stats
    return None, all_stats

Bool1 = [ Bool ]
Bool2 = [ Bool ] * 2
Bool3 = [ Bool ] * 3
Bool4 = [ Bool ] * 4

true0  = Op('true',   []   , Bool, lambda ins: True)
false0 = Op('false',  []   , Bool, lambda ins: False)

not1  = Op('not',     Bool1, Bool, lambda ins: Not(ins[0]))         #7404
nand2 = Op('nand2',   Bool2, Bool, lambda ins: Not(And(ins)))       #7400
nor2  = Op('nor2',    Bool2, Bool, lambda ins: Not(Or(ins)))        #7402
and2  = Op('and2',    Bool2, Bool, And)                             #7408
or2   = Op('or2',     Bool2, Bool, Or)                              #7432
xor2  = Op('xor2',    Bool2, Bool, lambda ins: Xor(ins[0], ins[1])) #7486

and3  = Op('and3',    Bool3, Bool, And)                             #7408
or3   = Op('or3',     Bool3, Bool, Or)                              #7432

nand3 = Op('nand3',   Bool3, Bool, lambda ins: Not(And(ins)))       #7410
nor3  = Op('nor3',    Bool3, Bool, lambda ins: Not(Or(ins)))        #7427
and3  = Op('and3',    Bool3, Bool, And)                             #7411

nand4 = Op('nand4',   Bool4, Bool, lambda ins: Not(And(ins)))       #7420
and4  = Op('and4',    Bool4, Bool, And)                             #7421
nor4  = Op('nor4',    Bool4, Bool, lambda ins: Not(Or(ins)))        #7429

mux2  = Op('mux2',    Bool2, Bool, lambda i: Or(And(i[0], i[1]), And(Not(i[0]), i[2])))
eq2   = Op('eq2',     Bool2, Bool, lambda i: i[0] == i[1])

class Bv:
    def __init__(self, width):
        self.width = width

        bitvec_ops = [
            (BitVecRef.__add__, self),
            (BitVecRef.__sub__, self),
            (BitVecRef.__mul__, self),
            (BitVecRef.__and__, self),
            (BitVecRef.__or__, self),
            (BitVecRef.__xor__, self),
            (BitVecRef.__mod__, self),
            (BitVecRef.__div__, self),
            (BitVecRef.__lt__, Bool),
            (BitVecRef.__le__, Bool),
            (BitVecRef.__gt__, Bool),
            (BitVecRef.__ge__, Bool),
        ]

        def create(op, ty, precond=lambda x: True):
            name = op.__name__.replace('_', '')
            return Op(name, [ self, self ], ty, lambda x: op(x[0], x[1]), precond=precond)

        # a loop that creates a field for each bit-vector operator in the class
        for o, ty in bitvec_ops:
            op = create(o, ty)
            setattr(self, op.name, op)

        shift_precond = lambda x: And([x[1] >= 0, x[1] < self.width])
        self.lshift = create(BitVecRef.__lshift__, self, shift_precond)
        self.rshift = create(BitVecRef.__rshift__, self, shift_precond)

    def __call__(self, name):
        return BitVec(name, self.width)

    def __str__(self):
        return f'Bv{self.width}'

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
    # sample function results
    random.seed(a=seed, version=2)
    clauses = []
    for vals in itertools.product(*[range(2)] * len(inputs)):
        if random.choice(range(100)) < clause_probability:
            clauses += [ And([ inp if pos else Not(inp) for inp, pos in zip(inputs, vals) ]) ]
    return Or(clauses)

class Tests:
    def __init__(self, max_length, debug, write_stats):
        self.debug = debug
        self.max_length = max_length
        self.write_stats = write_stats

    def do_synth(self, name, input_names, specs, ops):
        print(f'{name}: ', end='', flush=True)
        prg, stats = synth(specs, ops, self.max_length, \
                           from_len=0, input_names=input_names, debug=self.debug)
        total_time = sum(s['time'] for s in stats)
        print(f'{total_time / 1e9:.3f}s')
        if self.write_stats:
            with open(f'{name}.json', 'w') as f:
                json.dump(stats, f, indent=4)
        print(prg)
        return total_time

    def random_test(self, name, n_vars, create_formula):
        ops  = [ and2, or2, xor2, not1 ]
        spec = Op('rand', [ Bool ] * n_vars, Bool, create_formula)
        return self.do_synth(name, [ f'x{i}' for i in range(n_vars)], [spec], ops)

    def test_rand(self, size=40, n_vars=4):
        ops = [ (And, 2), (Or, 2), (Xor, 2), (Not, 1) ]
        f   = lambda x: create_random_formula(x, size, ops)
        return self.random_test('random formula', n_vars, f)

    def test_rand_dnf(self, n_vars=4):
        f = lambda x: create_random_dnf(x)
        return self.random_test('random dnf', n_vars, f)

    def test_and(self):
        spec = Op('and', Bool2, Bool, And)
        return self.do_synth('and', [ 'a', 'b'], [spec], [spec])

    def test_xor(self):
        spec = Op('xor2', Bool2, Bool, lambda i: Xor(i[0], i[1]))
        ops  = [ and2, nand2, or2, nor2 ]
        return self.do_synth('xor', [ 'x', 'y' ], [ spec ], ops)

    def test_mux(self):
        spec = Op('mux2', Bool3, Bool, lambda i: Or(And(i[0], i[1]), And(Not(i[0]), i[2])))
        ops  = [ and2, xor2 ]
        return self.do_synth('mux', [ 's', 'x', 'y' ], [ spec ], ops)

    def test_zero(self):
        spec = Op('zero', [ Bool ] * 8, Bool, lambda i: Not(Or(i)))
        ops  = [ and2, nand2, or2, nor2, nand3, nor3, nand4, nor4 ]
        return self.do_synth('zero', [ f'x{i}' for i in range(8) ], [ spec ], ops)

    def test_add(self):
        cy  = Op('cy',  Bool3, Bool, lambda i: Or(And(i[0], i[1]), And(i[1], i[2]), And(i[0], i[2])))
        add = Op('add', Bool3, Bool, lambda i: Xor(i[0], Xor(i[1], i[2])))
        ops = [ nand2, nor2, and2, or2, xor2 ]
        return self.do_synth('1-bit full adder', [ 'x', 'y', 'c' ], [ add, cy ], ops)

    def test_identity(self):
        spec = Op('magic', Bool1, Bool, lambda ins: And(Or(ins[0])))
        ops = [ nand2, nor2, and2, or2, xor2 ]
        return self.do_synth('identity', [ 'x' ], [ spec ], ops)

    def test_true(self):
        spec = Op('magic', Bool3, Bool, lambda ins: Or(Or(ins[0], ins[1], ins[2]), Not(ins[0])))
        ops = [ true0, false0, nand2, nor2, and2, or2, xor2 ]
        return self.do_synth('constant true', [ 'x', 'y', 'z' ], [ spec ], ops)

    def test_multiple_types(self):
        def Bv(v):
            return BitVec(v, 8)
        def BvLong(v):
            return BitVec(v, 16)
        int2bv = Op('int2bv', [ Int ], BvLong, lambda x: Int2BV(x[0], 16))
        bv2int = Op('bv2int', [ Bv ], Int, lambda x: BV2Int(x[0]))
        div2   = Op('div2', [ Int ], Int, lambda x: x[0] / 2)
        spec   = Op('shr2', [ Bv ], BvLong, lambda x: LShR(ZeroExt(8, x[0]), 1))
        ops    = [ int2bv, bv2int, div2 ]
        return self.do_synth('multiple types', [ 'x' ], [ spec ], ops)

    def test_precond(self):
        def Bv(v):
            return BitVec(v, 8)
        int2bv = Op('int2bv', [ Int ], Bv, lambda x: Int2BV(x[0], 8))
        bv2int = Op('bv2int', [ Bv ], Int, lambda x: BV2Int(x[0]))
        mul2   = Op('addadd', [ Bv ], Bv, lambda x: x[0] + x[0])
        spec   = Op('mul2', [ Int ], Int, lambda x: x[0] * 2, \
                    precond=lambda x: And([x[0] >= 0, x[0] < 128]))
        ops    = [ int2bv, bv2int, mul2 ]
        return self.do_synth('preconditions', [ 'x' ], [ spec ], ops)

    def test_constant(self):
        mul    = Op('mul', [ Int, Int ], Int, lambda x: x[0] * x[1])
        spec   = Op('const', [ Int ], Int, lambda x: x[0] + x[0])
        return self.do_synth('constant', [ 'x' ], [ spec ], [ mul ])

    def test_abs(self):
        bv = Bv(32)
        ops  = [ bv.sub, bv.xor, bv.rshift, ]
        spec = Op('spec', [ bv ], bv, lambda x: If(x[0] >= 0, x[0], -x[0]))
        return self.do_synth('abs', [ 'x' ], [ spec ], ops)

    def test_array(self):
        def Arr(name):
            return Array(name, IntSort(), IntSort())

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

        ops = [
            Op('swap', [ Arr, Int ], Arr, lambda x: swap(x[0], x[1], x[1] + 1)),
        ]
        spec = Op('rev', [ Arr ], Arr, lambda x: permutation(x[0], [3, 2, 1, 0]))
        return self.do_synth('array', [ 'a' ], [ spec ], ops)

    def run(self, tests=None):
        # iterate over all methods in this class that start with 'test_'
        if tests is None:
            tests = [ name for name in dir(self) if name.startswith('test_') ]
        else:
            tests = [ 'test_' + s for s in tests.split(',') ]
        total_time = 0
        for name in tests:
            total_time += getattr(self, name)()
            print('')
        print(f'total time: {total_time / 1e9:.3f}s')


if __name__ == "__main__":
    set_param("parallel.enable", True)
    import argparse
    parser = argparse.ArgumentParser(prog="synth")
    parser.add_argument('-d', '--debug', type=int, default=0)
    parser.add_argument('-m', '--maxlen', type=int, default=10)
    parser.add_argument('-s', '--stats', default=False, action='store_true')
    parser.add_argument('-t', '--tests', default=None, type=str)
    args = parser.parse_args()

    tests = Tests(args.maxlen, args.debug, args.stats)
    tests.run(args.tests)