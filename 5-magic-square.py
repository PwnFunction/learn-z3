#!/usr/bin/env python3
import z3
from itertools import chain

"""
A square array of numbers, usually positive integers, is called a magic square
if the sums of the numbers in each row, each column, and both main diagonals are the same.

Magic square of 15 looks like:
8 1 6
3 5 7
4 9 2
"""

x = [[z3.Int(f'x_{i}_{j}') for i in range(3)] for j in range(3)]

range_c = [z3.And(i >= 1, i <= 9) for i in chain(*x)]
unique_c = [z3.Distinct([i for i in chain(*x)])]
row_c = [sum(i) == 15 for i in x]
column_c = [sum(list(chain(*x))[i::3]) == 15 for i in range(3)]
diagonal_c = [x[0][0]+x[1][1]+x[2][2] == 15,
              x[0][2]+x[1][1]+x[2][0] == 15]

magic_c = range_c + unique_c + row_c + column_c + diagonal_c

solver = z3.Solver()
solver.add(magic_c)

if solver.check() == z3.sat:
    m = solver.model()
    r = [[m.evaluate(x[i][j]) for i in range(3)] for j in range(3)]
    for i in r:
        print(' '.join(map(str, i)))
