#!/usr/bin/env python3
import z3

"""
// lowercase
private static boolean hash(final String s) {
    int n = 7;
    final int n2 = 593779930;
    for(int i = 0; i < 6; ++i) {
        n = n * 31 + s.charAt(i);
    }
    return n == n2;
}
"""

n = 7
letters = [z3.Int(f's_{i}') for i in range(6)]

for i in letters:
    n = n * 31 + i

solver = z3.Solver()

for i in letters:
    solver.add(z3.And(i >= ord('a'), i <= ord('z')))

solver.add((n % 2**32) == 593779930)

if solver.check() == z3.sat:
    m = solver.model()
    s = ''
    for i in letters:
        s += (f'{chr(m.evaluate(i).as_long())}')
    print(s)
