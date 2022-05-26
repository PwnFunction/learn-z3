#!/usr/bin/env python3
import z3
from itertools import chain

"""
Solve the sudoku

0 0 0 0 9 4 0 3 0
0 0 0 5 1 0 0 0 7
0 8 9 0 0 0 0 4 0
0 0 0 0 0 0 2 0 8
0 6 0 2 0 1 0 5 0
1 0 2 0 0 0 0 0 0
0 7 0 0 0 0 5 2 0
9 0 0 0 6 5 0 0 0
0 4 0 9 7 0 0 0 0
"""

x = [[z3.Int(f'x_{i}_{j}') for i in range(9)] for j in range(9)]

range_c = [z3.And(i >= 1, i <= 9) for i in chain(*x)]

instance = ((0, 0, 0, 0, 9, 4, 0, 3, 0),
            (0, 0, 0, 5, 1, 0, 0, 0, 7),
            (0, 8, 9, 0, 0, 0, 0, 4, 0),
            (0, 0, 0, 0, 0, 0, 2, 0, 8),
            (0, 6, 0, 2, 0, 1, 0, 5, 0),
            (1, 0, 2, 0, 0, 0, 0, 0, 0),
            (0, 7, 0, 0, 0, 0, 5, 2, 0),
            (9, 0, 0, 0, 6, 5, 0, 0, 0),
            (0, 4, 0, 9, 7, 0, 0, 0, 0))
instance_c = [z3.If(instance[i][j] == 0, True, instance[i][j] == x[i][j])
              for i in range(9) for j in range(9)]

row_c = [z3.Distinct(i) for i in x]

column_c = [z3.Distinct(list(chain(*x))[i::9]) for i in range(9)]

square_c = [z3.Distinct([x[j + l][i + k] for l in range(3) for k in range(3)])
            for j in range(0, 9, 3) for i in range(0, 9, 3)]

sudoku_c = range_c + instance_c + row_c + column_c + square_c

solver = z3.Solver()
solver.add(sudoku_c)

if solver.check() == z3.sat:
    m = solver.model()
    r = [[m.evaluate(x[j][i]) for i in range(9)] for j in range(9)]
    for i in r:
        print(' '.join(map(str, i)))
