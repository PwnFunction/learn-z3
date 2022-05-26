#!/usr/bin/env python3
import z3

"""
x + 2y = 7 where x > 2 and y < 10
"""
x, y = z3.Ints('x y')

solver = z3.Solver()

solver.add(x + 2*y == 7)
solver.add(x > 2)
solver.add(y < 10)

if solver.check() == z3.sat:
    print(solver.model())
