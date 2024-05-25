import pysmt.typing
from pysmt.shortcuts import *
from pysmt.environment import Environment, push_env, pop_env
from pysmt.fnode import FNode
from pysmt.solvers.solver import Solver

push_env()
env1: Environment = get_env()
res1: FNode = FreshSymbol(BVType(3))
x: FNode = Symbol('x', BVType(3))
phi1: FNode = Equals(res1, BVAdd(x, BV(5, 3)))
push_env()
env2: Environment = get_env()
res2: FNode = FreshSymbol(BVType(3))
y: FNode = Symbol('y', BVType(3))
phi2: FNode = Equals(res2, BVAdd(y, BV(3, 3)))
res2_1: FNode = env1.formula_manager.normalize(res2)
# This pop_env seems to be the key to success, substitute seems to use the formula manager of the top env of the stack
# not the formula's env
pop_env()
phi1_mod: FNode = phi1.substitute({x: res2_1})
solver: Solver = pysmt.shortcuts.Solver('z3', 'QF_AUFBV')
solver.add_assertions([phi1, phi1_mod, phi2])
res = solver.solve()
if res:
    print(solver.get_model())
if not res:
    print('Could not solve Solver')

