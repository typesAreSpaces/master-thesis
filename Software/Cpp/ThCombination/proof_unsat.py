#!/usr/bin/env python 

from z3 import *

set_param(proof=True)
# set_pp_option("max_indent", 0)
#set_pp_option("max_width", 10000)
Z = IntSort()
x1, x2, x3 = Ints("x1 x2 x3")
f = Function("f", Z, Z, Z)

s = Solver()
print s.help()
# s.set(mbqi=True)
# s.push()
# s.add(f(x1, 0) >= x3)
# s.add((x3- f(x1, 0)) >= 1)
# if (s.check() == unsat):
#     print s.proof()
# s.pop()

s.push()
# print s.help()
B = BoolSort()
p = Function("p", Z, B)
a, b, x = Ints("a b x")
s.add(1 <= x)
s.add(x <= 2)
s.add(a == 1)
s.add(b == 2)
s.add(p(x))
s.add(Not(p(a)))
s.add(Not(p(b)))
if (s.check() == unsat):
    print s.proof()
    
s.pop()
