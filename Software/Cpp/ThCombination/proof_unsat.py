#!/usr/bin/env python 

from z3 import *

set_param(proof=True)
set_param(v2=True)

Z = IntSort()
x1, x2, x3 = Ints("x1 x2 x3")
f = Function("f", Z, Z, Z)

s = Solver()
# s.set(mbqi=True)
# s.push()
# s.add(f(x1, 0) >= x3)
# s.add((x3- f(x1, 0)) >= 1)
# if (s.check() == unsat):
#     print s.proof()
# s.pop()

s.push()
print s.help()
B = BoolSort()
p = Function("p", Z, B)
a1, a2, a3, x = Ints("a1 a2 a3 x")
s.add(1 <= x)
s.add(x <= 2)
s.add(a1 == 1)
s.add(a2 == 2)
s.add(p(x))
s.add(Not(p(a1)))
s.add(Not(p(a2)))
if (s.check() == unsat):
    print s.proof()
    
s.pop()
