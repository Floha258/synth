import re
from z3 import *


# Function to convert SMT-LIB expression to Z3
def smtlib_to_z3(expression: str, dict):
    # Regex to match the structure of the expression
    array_pattern = re.compile(r'\(define-fun (\w+) \(\) \(Array (\w+) (\w+)\) (.+)\)')
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
                tokens.pop(0) # negative numbers are in parantheses, therefore we need to pop the closing paranthesis
                return IntVal(int(token[0] + token[2:]))  # remove space between - and number
            expr = IntVal(int(token))
            return expr
        else:
            return Int(token)  # assuming the token is an integer variable or value


    # Initialize parsing from the root expression
    z3_expr = parse_expression(tokens)

    # Return the constructed Z3 expression
    return z3_expr


# Example usage
expression = "(define-fun x () (Array Int Int) (store (store (store ((as const (Array Int Int)) 0) 0 1) 2 (- 1)) 1 (- 2)))"
z3_expr = smtlib_to_z3(expression)
print(z3_expr)

# Another example with as const
expression_const = "(define-fun x () (Array Int Int) ((as const (Array Int Int)) 0))"
z3_expr_const = smtlib_to_z3(expression_const)
print(z3_expr_const)
