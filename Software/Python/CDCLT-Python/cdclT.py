from z3 import *

def simple_cdclT(clauses):
    prop_solver   = Solver()
    theory_solver = Solver()

    # abs : atomic predicate -> propositional abstraction
    abs = {} 

    prop_solver  .add(abstract_clauses(abs, clauses))
    theory_solver.add([p == abs[p] for p in abs])

    while True:
        is_sat = prop_solver.check()
        if sat == is_sat:
            m    = prop_solver.model()
            lits = [mk_lit(m, abs[p]) for p in abs]
            if unsat == theory_solver.check(lits):
                conflict_clause = Not(And(theory_solver.unsat_core()))
                print('Conflict clause found: {}'.format(conflict_clause))
                prop_solver.add(conflict_clause)
            else:
                print('Result: sat')
                print('Model:\n{}'.format(theory_solver.model()))
                print('Abstraction:\n{}'.format(abs));
                return
        else:
            print('Result: unsat')
            print('Abstraction:\n{}'.format(abs));
            return

index = 0
def abstract_atom(abs, atom):
    global index
    if atom in abs:
        return abs[atom]
    p = Bool('p{}'.format(index))
    index += 1
    abs[atom] = p
    return p

def abstract_lit(abs, lit):
    if is_not(lit):
        return Not(abstract_atom(abs, lit.arg(0)))
    return abstract_atom(abs, lit)

def abstract_clause(abs, clause):
    return Or([abstract_lit(abs, lit) for lit in clause])

def abstract_clauses(abs, clauses):
    return [abstract_clause(abs, clause) for clause in clauses]

def mk_lit(m, p):
    if is_true(m.eval(p)):
        return p
    else:
        return Not(p)
