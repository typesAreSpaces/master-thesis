from z3 import *

def cdclT(clauses):
    prop_solver   = Solver()
    theory_solver = Solver()

    # abstractions : atomic predicate -> propositional abstraction
    # concretes    : propositional abstraction -> atomic predicate 
    abstractions = {} 
    concretes    = {}

    prop_solver  .add(abstract_clauses (abstractions, concretes, clauses))
    theory_solver.add([Or(clause) for clause in clauses])

    while True:
        is_sat = prop_solver.check()
        if sat == is_sat:
            partial_model = prop_solver.model()
            lits          = mk_lits(partial_model, concretes)
            if unsat == theory_solver.check(lits):
                unsat_cores = theory_solver.unsat_core()
                prop_solver.add(abstract_conflict_clause(abstractions, concretes, unsat_cores))
                # --------------------------------------------------------
                # TODO: store the conflict clauses somewhere
                # in order to compute 
                # partial conflict clauses interpolants later
                conflict_clause = Not(And(unsat_cores))
                print('Conflict clause found: {}'.format(conflict_clause))
                # --------------------------------------------------------
            else:
                print('Result: sat')
                print('Model:\n{}'.format(theory_solver.model()))
                return
        else:
            print('Result: unsat')
            return

index  = 0
def abstract_atom (abstractions, concretes, atom):
    global index 
    if atom in abstractions:
        return abstractions[atom]
    p = Bool('p{}'.format(index ))
    index += 1
    abstractions[atom] = p
    concretes[p]       = atom
    return p

def abstract_lit (abstractions, concretes, lit):
    if is_not(lit):
        return Not(abstract_atom (abstractions, concretes, lit.arg(0)))
    return abstract_atom (abstractions, concretes, lit)

def abstract_clause (abstractions, concretes, clause):
    return Or([abstract_lit (abstractions, concretes, lit) for lit in clause])

def abstract_clauses (abstractions, concretes, clauses):
    return [abstract_clause (abstractions, concretes, clause) for clause in clauses]

def mk_lits(m, concretes):
    result = []
    for prop in concretes:
        if(is_true(m.eval(prop))):
            result.append(concretes[prop])
        else:
            result.append(Not(concretes[prop]))
    return result

def abstract_conflict_clause(abstractions, concretes, unsat_cores):
    result = []
    for lit in unsat_cores:
        result.append(abstract_lit (abstractions, concretes, lit))
    return Not(And(result))
