from os import path, makedirs, remove
import subprocess
import time
from enum import Enum
from contextlib import contextmanager
import re
from z3 import BitVecVal, BoolVal, Solver, Array, IntSort, K, Store, IntVal, Int, ExprRef, Tactic, simplify


# from oplib import Bv


@contextmanager
def timer():
    start = time.perf_counter_ns()
    yield lambda: time.perf_counter_ns() - start


class SupportedSolvers(Enum):
    CVC: str = 'cvc5'
    YICES: str = 'yices'
    Z3: str = 'z3'


def write_smt2(filename: str, solver, ctx=None, logic='ALL'):
    if logic is None:
        logic = 'ALL'
    s = solver
    if not type(s) is Solver:
        s = Solver(ctx=solver.ctx)
        t = Tactic('card2bv', ctx=ctx)
        for a in solver:
            for b in t(simplify(a)):
                s.add(b)
    if filename:
        file_dir = path.join(path.dirname(__file__), 'smt2')
        makedirs(file_dir, exist_ok=True)
        filepath = path.join(file_dir, filename)

        with open(filepath, 'w') as f:
            print(f'(set-logic {logic})', file=f)
            print(s.to_smt2(), file=f)
            print('(get-model)', file=f)


def solve_smtlib(filename: str, solver: SupportedSolvers) -> tuple[bool, int, list[str]]:
    file_dir = path.join(path.dirname(__file__), 'smt2')
    filepath = path.join(file_dir, filename)
    with timer() as elapsed:
        if solver.value == 'z3':
            res = subprocess.run(['z3', filepath], capture_output=True).stdout.decode('utf-8').strip()
        elif solver.value == 'yices':
            res = subprocess.run(['yices-smt2', filepath],
                                 capture_output=True).stdout.decode('utf-8').strip()
        else:
            res = subprocess.run(['cvc5', filepath, '--produce-models', f'--tlimit={5 * 60 * 1000}'], capture_output=True).stdout.decode(
                'utf-8').strip()
        solveTime = elapsed()
    resLines = res.split('\r\n')
    if resLines[0] == 'sat':
        res = True
    elif resLines[0] == 'unsat':
        res = False
    else:
        raise Exception(resLines[0], filename)
    for i in resLines:
        if 'Types' in i:
            print('break')
    remove(f'smt2/{filename}')
    return res, solveTime, resLines[1:]


def extract_model_cvc(output: list[str]) -> dict:
    # Original RegEx generated by ChatGPT, 25/07/2024, modified by myself
    pattern = re.compile(
        r'\(define-fun (\|[\w|()_]+\|?|[\w|_]+) \(\) \(?_? ?(\w+) ?(\d*)\)? ?(true|false|#b[01]+|\(?-? ?\d+\)?|\w+|\|Array\(\w+, \w+\)\|)\)')
    model_dict = {}

    # Pattern Finding generated by ChatGPT, 25/07/2024, modified by myself
    for line in output:
        match = pattern.match(line)
        if 'Array' in line and 'Types' not in line:
            variable_name, expr = smtlib_array_to_z3(line)
            model_dict[variable_name] = (expr,)
        elif match:
            variable_name = match.group(1)
            type_name = match.group(2)
            bit_width = match.group(3) if match.group(3) else ''  # Handle optional bit width
            value = match.group(4)
            model_dict[variable_name] = (type_name, bit_width, value)

    return model_dict


def extract_model_yices(output: list[str]) -> dict:
    bv_regex = r'#b\d+'
    bv_pattern = re.compile(bv_regex)
    bool_regex = r'true|false'
    bool_pattern = re.compile(bool_regex)
    int_regex = r'\d+|\(- \d+\)'
    int_pattern = re.compile(int_regex)
    pattern = re.compile(rf'\(= (\S+) ({bv_regex}|{bool_regex}|{int_regex})\)')

    model_dict = {}

    # Pattern Finding generated by ChatGPT, 25/07/2024, modified by myself
    for line in output:
        match = pattern.match(line)
        # if 'Array' in line and 'Types' not in line:
        #     variable_name, expr = smtlib_array_to_z3(line)
        #     model_dict[variable_name] = (expr,)
        if match:
            variable_name = match.group(1)
            value = match.group(2)
            if bool_pattern.match(value):
                type_name = 'Bool'
                bit_width = None
            elif bv_pattern.match(value):
                type_name = 'BitVec'
                bit_width = len(value[2:])
            elif int_pattern.match(value):
                type_name = 'Int'
                bit_width = None
            else:
                raise ValueError('invalid expression', line)
            model_dict[variable_name] = (type_name, bit_width, value)
        else:
            raise ValueError("Invalid expression format", line)

    return model_dict


def extract_model_z3(output: list[str]) -> dict:
    # RegEx generated by ChatGPT, 10/08/2024
    pattern = re.compile(r'\(define-fun (\|[\w|()_]+\|?|[\w|_]+) \(\) \(?_? ?(\w+) ?(\d*)\)?\s+(\S+)\)')
    model_dict = {}

    # Pattern Finding generated by ChatGPT, 10/08/2024
    i = 0
    while i < len(output):
        match = re.match(pattern, "\n".join(output[i:i + 2]).strip())
        if match:
            variable_name = match.group(1)
            type_name = match.group(2)
            bit_width = match.group(3) if match.group(3) else ''  # Handle optional bit width
            value = match.group(4)
            model_dict[variable_name] = (type_name, bit_width, value)
            i += 2  # Skip the next line as it's already processed
        else:
            i += 1  # Move to the next line
    return model_dict


# Function to convert SMT-LIB expression to Z3
def smtlib_array_to_z3(expression: str) -> (str, ExprRef):
    # Regex to match the structure of the expression
    array_pattern = re.compile(r'\(define-fun (\|?\w+\|?|\S+\(.*\)\S+) \(\) \(Array (\w+) (\w+)\) (.+)\)')
    # store_pattern = re.compile(r'\(|\)|-?\d+|\w+')
    store_pattern = re.compile(r'\(|\)|-? ?\d+|\w+')

    # Extract the components of the define-fun expression
    match = array_pattern.match(expression)
    if not match:
        raise ValueError("Invalid expression format")

    # Extracting the variable name, array type, and operations
    variable_name = match.group(1)
    operations = match.group(4)

    # Tokenizing the operations
    tokens = store_pattern.findall(operations)

    # Recursively parse the expression to build the Z3 equivalent
    def parse_expression(tokens):
        token = tokens.pop(0).strip()
        if token == "(":
            expr = parse_expression(tokens)
            # tokens.pop(0)
            return expr
        elif token == "store":
            array_expr = parse_expression(tokens)
            index = parse_expression(tokens)
            value = parse_expression(tokens)
            tokens.pop(0)  # pop the closing parenthesis ')'
            return Store(array_expr, index, value)
        elif token == "as":
            # skip const (Array (Int Int)), 7 pops
            tokens.pop(0)
            tokens.pop(0)
            tokens.pop(0)
            tokens.pop(0)
            tokens.pop(0)
            tokens.pop(0)
            tokens.pop(0)
            const_val = parse_expression(tokens)
            tokens.pop(0)  # pop the closing parenthesis ')'
            return K(IntSort(), const_val)
        elif token == ")":
            return None  # This should not happen, '(' and ')' are handled in the recursion
        elif token.isdigit() or re.match(r'(- )?\d+', token):
            if token[0] == '-':
                tokens.pop(0)  # negative numbers are in parantheses, therefore we need to pop the closing paranthesis
                return IntVal(int(token[0] + token[2:]))  # remove space between - and number
            expr = IntVal(int(token))
            return expr
        else:
            return Int(token)  # assuming the token is an integer variable or value

    # Initialize parsing from the root expression
    z3_expr = parse_expression(tokens)

    # Return the constructed Z3 expression
    return variable_name, z3_expr


def _eval_model(model: list[str], vars, ctx, solver: SupportedSolvers):
    if solver.value == 'cvc5':
        m = extract_model_cvc(model)
    elif solver.value == 'yices':
        m = extract_model_yices(model)
    else :
        m = extract_model_z3(model)
    res = []

    for v in vars:
        # CVC (and maybe other solvers) remove the pipes if they're not needed. Therefore we check for pipes and remove
        # them if not needed, so we can correctly get the value from the output
        v = str(v)
        if '(' not in v and ')' not in v and '|' in v:
            # no brackets in v but pipes, means we have to remove the pipes
            v = v[1:-1]

        if v not in m:
            res.append(BoolVal(True, ctx))
            break

        if len(m[v]) == 1:
            res.append(m[v][0])
            break

        type, width, value = m[v]

        if type == 'BitVec':
            if value[0:2] == '#b':
                val = int(value.split('#b')[1], 2)
            elif value[0:2] == '#x':
                val = int(value.split('#x')[1], 16)
            w = int(width)
            res.append(BitVecVal(val, w, ctx))
        elif type == 'Int':
            if value[0] == '(':
                value = value[1] + value[3:-1]  # remove the brackets and space for neg ints
            res.append(IntVal(int(value)))
        elif type == 'Operators':
            res.append(value)
        elif type[0:5] == 'Array':
            arrayRegex = re.compile(r'\(as const \(Array \w+ \w+\)\) (\w+)')
            match = arrayRegex.search(value)
            if match:
                const_val = match.group(1)
                res.append(K(IntSort(), int(const_val)))
            else:
                raise Exception(f'Cannot find const array value in {value}')
        else:
            res.append(BoolVal(value == 'true', ctx))
    return res
