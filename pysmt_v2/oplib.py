from pysmt.shortcuts import Symbol, Not, And, Or, Xor, EqualsOrIff, BVType, BV, BVUDiv, BVURem, BVSRem, BVLShr, Ite, \
    BVUGE, BVULT, BVSGE, BVSLT
from cegis import Func


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
            Func('sge', Ite(BVSGE(x, y), o, z)),
            Func('slt', Ite(BVSLT(x, y), o, z)),
        ]

        for op in l:
            setattr(self, f'{op.name}_', op)