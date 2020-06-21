from z3 import *

set_option(proof=True)

def print_proof(formula):
    s = Solver()
    s.add(formula)
    if(s.check() == unsat):
        print('Refutational proof found:')
        print(s.proof())
    else:
        print('No refutational proof was found')
