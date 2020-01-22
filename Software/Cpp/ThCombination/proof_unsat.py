#!/usr/bin/env python 

from z3 import *

set_param(proof=True)

Z = IntSort()
x1, x2, x3 = Ints("x1 x2 x3")
f = Function("f", Z, Z, Z)

s = Solver()
s.push()
s.add(f(x1, 0) >= x3)
s.add((x3- f(x1, 0)) >= 1)
if (s.check() == unsat):
    print s.proof()
s.pop()

s.push()
B = BoolSort()
p = Function("p", Z, B)
s.add(1 <= x1)
s.add(x1 <= 2)
s.add(p(x1))
s.add(Not(p(1)))
s.add(Not(p(2)))
if (s.check() == unsat):
    print s.proof()
    
s.pop()
