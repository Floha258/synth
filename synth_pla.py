#! /usr/bin/env python3

from synth_alt import *

def read_pla(pla_string):

    plain_constraints = []

    for line in pla_string.split("\n"):
        line = line.strip()
        if line.startswith(".o "):
            assert line.split(" ")[1] == "1", "only one output bit is currently supported"
            continue
        elif line.startswith(".i "):
            num_vars = int(line.split(" ")[1])
            params = [ Bool(f'i{i}') for i in range(num_vars) ]
            continue
        elif line.startswith(".") or line == "":
            continue

        assert num_vars != -1, "PLA needs to contain number of inputs"

        constraint, result = line.split(" ")
        if result == "0": continue # 0-lines are also often omitted.
        assert result == "1", "unknown result in clause"

        plain_constraints.append(constraint)

    def wrapper(params):
        clauses = []
        for n, constraint in enumerate(plain_constraints):
            clause = []
            if n % 1000 == 0:
                print(f"processing clause {n}")

            for i, literal in enumerate(constraint):
                if literal == "-":
                    continue
                elif literal == "1":
                    clause.append(params[i])
                elif literal == "0":
                    clause.append(Not(params[i]))
                else:
                    assert False, "invalid character in constraint"

            clause = And(clause)
            clauses.append(clause)
        return Or(clauses)
    return params, wrapper

def test_pla(filename):
    with open(filename) as f:
        pla = f.read()

    params, formula = read_pla(pla)
    spec = Op('spec', [ Bool ] * len(params), Bool, formula)
    ops  = [ true0, false0, and3, or3, and2, or2, xor2, not1 ]
    prg = synth_smallest(10, [ str(p) for p in params ], [spec], ops, 1)
    print(prg)

test_pla(sys.argv[1])

