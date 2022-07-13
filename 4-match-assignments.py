#!/usr/bin/env python3
import z3

"""
There is an assignment of unique digits to letters such that the equation `send + more = money` holds. 
Find an assignment of the digits to make this true.
"""

digits = z3.Ints('o d n m e y s r')
o, d, n, m, e, y, s, r = digits


def join_numbers(l):
    return z3.Sum([10**i * v for i, v in enumerate(l[::-1])])


send = join_numbers([s, e, n, d])
more = join_numbers([m, o, r, e])
money = join_numbers([m, o, n, e, y])

solver = z3.Solver()

solver.add(z3.Distinct(digits))
solver.add(send + more == money)
solver.add([z3.And(i >= 0, i <= 9) for i in digits])
solver.add([s > 0, m > 0])

if solver.check() == z3.sat:
    m = solver.model()
    print(f'{m}\n{m.eval(send)} + {m.eval(more)} = {m.eval(money)}')
