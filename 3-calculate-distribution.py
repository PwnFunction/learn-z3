#!/usr/bin/env python3
import z3

"""
Spend exactly 100 dollars and buy exactly 100 animals. 
Dogs cost 15 dollars, cats cost 1 dollar, and mice cost 25 cents each. 
You have to buy at least one of each. How many of each should you buy?
"""

d, c, m = z3.Ints('d c m')

solver = z3.Solver()
solver.add(1500 * d + 100 * c + 25 * m == 10000)
solver.add(d + c + m == 100)
solver.add(d >= 1, c >= 1, m >= 1)

if solver.check() == z3.sat:
    print(solver.model())
