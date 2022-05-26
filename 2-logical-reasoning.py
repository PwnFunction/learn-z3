#!/usr/bin/env python3
import z3

"""
John, Aries, and Joseph are brothers with different ages. Who is the youngest if the following statements are true?

I. Aries is the oldest.
II. John is not the youngest.
"""

"""
Ages: 0 1 2
"""


def min(li):
    m = li[0]
    for i in li[1:]:
        m = z3.If(i < m, i, m)
    return m


def max(li):
    m = li[0]
    for i in li[1:]:
        m = z3.If(i > m, i, m)
    return m


john, aries, joseph = z3.Ints('john aries joseph')
bros = [john, aries, joseph]

solver = z3.Solver()

solver.add(z3.Distinct(bros))
solver.add([z3.And(i >= 0, i <= 2) for i in bros])

solver.add(aries == max(bros))
solver.add(joseph != min(bros))

if solver.check() == z3.sat:
    print(solver.model())
