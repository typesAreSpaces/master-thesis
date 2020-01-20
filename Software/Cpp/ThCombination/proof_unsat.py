#!/usr/bin/env python 

from z3 import *

set_param(proof=True)
Z = IntSort()
x1, x2, x3 = Ints("x1 x2 x3")
# f = Function("f", Z, Z)
f = Function("f", Z, Z, Z)
s = Solver()
# s.add(x2 >= x1)
# s.add(x1 - x3 >= x2)
# s.add(x3 >= 0)
# s.add(f(f(x1) - f(x2)) != f(x3))
s.add(f(x1, 0) >= x3)
# s.add(f(x2, 0) <= x3)
# s.add(x1 >= x2)
# s.add(x2 >= x1)
s.add((x3- f(x1, 0)) >= 1)

print s.check()
print s.proof()
