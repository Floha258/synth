import time

from smtlib import SupportedSolvers, write_smt2, solve_smtlib, _eval_model

from contextlib import contextmanager
from functools import cached_property

from z3 import *

from spec import Eval, Spec


class OpFreq:
    MAX = 1000000000


class Prg:
    def __init__(self, ctx, insns, outputs, out_vars, in_vars, solver=SupportedSolvers.CVC):
        """Creates a program.

        Attributes:
        spec: The original specification
        insns: List of instructions.
            This is a list of pairs where each pair consists
            of an Op and a list of pairs that denotes the arguments to
            the instruction. The first element of the pair is a boolean
            that indicates whether the argument is a constant or not.
            The second element is either the variable number of the
            operand or the constant value of the operand.
        outputs: List of outputs.
            For each output variable in `spec` there is a tuple
            `(is_const, v)` in this list. `is_const` indicates that
            the output is constant. In this case, `v` is a Z3 constant
            that gives the value of the constant output. If `is_const`
            is false, `v` is a Python int that indicates the number of
            the instruction in this program whose value is the output.
            Note that the first n numbers are taken by the n inputs
            of the program.
        """
        assert all(insn.ctx == ctx for insn, _ in insns)
        self.ctx = ctx
        self.insns = insns
        self.outputs = outputs
        self.output_names = [ str(v) for v in out_vars ]
        self.input_names  = [ str(v) for v in in_vars ]
        self.out_vars = out_vars
        self.in_vars = in_vars
        self.solver = solver
        # this map gives for every temporary/input variable
        # which output variables are set to it
        self.output_map = { }
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
        vars = list(self.in_vars)
        n_inputs = len(vars)
        def get_val(p):
            is_const, v = p
            assert is_const or v < len(vars), f'variable out of range: {v}/{len(vars)}'
            return v if is_const else vars[v]
        for i, (insn, opnds) in enumerate(self.insns):
            assert insn.ctx == self.ctx
            subst = [ (i, get_val(p)) \
                      for i, p in zip(insn.inputs, opnds) ]
            res = Const(self.var_name(i + n_inputs), insn.func.sort())
            vars.append(res)
            yield res == substitute(insn.func, subst)
        for o, p in zip(self.out_vars, self.outputs):
            yield o == get_val(p)

    @cached_property
    def eval(self):
        s = Solver(ctx=self.ctx)
        for p in self.eval_clauses():
            s.add(p)
        return Eval(self.in_vars, self.out_vars, s)

    def __str__(self):
        n_inputs   = len(self.input_names)
        all_names  = [ self.var_name(i) for i in range(len(self) + n_inputs) ]
        max_len    = max(map(len, all_names))
        max_op_len = max(map(lambda x: len(x[0].name), self.insns), default=0)
        jv = lambda args: ', '.join(str(v) if c else self.var_name(v) for c, v in args)
        res = []
        for i, names in self.output_map.items():
            if i < n_inputs:
                res += [ f'{n:{max_len}} = {self.input_names[i]}' for n in names ]
        for i, (op, args) in enumerate(self.insns):
            y = self.var_name(i + n_inputs)
            res += [ f'{y:{max_len}} = {op.name:{max_op_len}} ({jv(args)})' ]
        for names in self.output_map.values():
            for n in names[1:]:
                res += [ f'{n:{max_len}} = {names[0]}']
        for n, (is_const, v) in zip(self.output_names, self.outputs):
            if is_const:
                res += [ f'{n:{max_len}} = {v}' ]
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
    { ' -> '.join([str(i) for i in range(n_inputs)])};
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

def cegis(spec: Spec, synth, init_samples=[], debug=no_debug, solver=SupportedSolvers.CVC):
    d = debug

    samples = init_samples if init_samples else spec.eval.sample_n(1)
    assert len(samples) > 0, 'need at least 1 initial sample'

    # set up the verification constraint
    verif = Solver(ctx=spec.ctx)
    verif.add(spec.precond)
    verif.add(Not(spec.phi))

    i = 0
    stats = []
    while True:
        stat = {}
        stats += [ stat ]
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

        if not prg is None:
            # we got a program, so check if it is correct
            stat['prg'] = str(prg).replace('\n', '; ')
            d(2, 'program:', stat['prg'])

            # push a new verification solver state
            # and add equalities that evaluate the program
            verif.push()
            for c in prg.eval_clauses():
                verif.add(c)

            filename = f'{spec.name}_verif_{samples_str}.smt2'
            write_smt2(filename, verif)
            d(3, 'verif', samples_str, verif)
            res, verif_time, model = solve_smtlib(filename, solver)
            stat['verif_time'] = verif_time
            d(2, f'verif time {verif_time / 1e9:.3f}')

            if res:
                # there is a counterexample, reiterate
                samples = [ _eval_model(model, spec.inputs, verif.ctx, solver) ]
                d(4, 'verification model', model)
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