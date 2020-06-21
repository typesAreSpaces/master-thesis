#!/usr/bin/env python
from cdclT       import simple_cdclT
from print_proof import print_proof
from z3          import *

Z = IntSort()
B = BoolSort()
x, y = Ints('x y')
p = Function('p', Z, B)
x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12 = Bools('x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12')

example_1 = [[x >= 0], [y == x + 1], [y > 2, y < 1]]
example_2 = [[1 <= x], [x <= 2], [p(x)], [Not(p(1))], [Not(p(2))]]
example_3 = [[1 == x, x == 2], [p(x)], [Not(p(1))], [Not(p(2))]]
example_4 = [[1 <= x], [x <= 2], [1 == x, x == 2], [p(x)], [Not(p(1))], [Not(p(2))]]
example_5 = [[x1, x4],[x1, Not(x3), Not(x8)],[x1, x8, x12],[x2, x11],[Not(x7), Not(x3), x9],[Not(x7), x8, Not(x9)],[x7, x8, Not(x10)],[x1, x10, Not(x12)]]
example_6 = [[x1, x2],[x1, Not(x2)],[Not(x1), x3],[Not(x1), Not(x3)]]
example_7 = [[x >= 10, y + x == 192],[x >= 10, Not(y + x == 192)],[Not(x >= 10), x - y < 0],[Not(x >= 10), Not(x - y < 0)]]

simple_cdclT(example_4)

# print_proof([Or(clause) for clause in example_5])
