#ifndef _CDCL_T_
#define _CDCL_T_
#define _DEBUG_CDCL_T_ 0

#include <iostream>
#include <fstream>
#include <z3++.h>

class CDCL_T {
  unsigned abstraction_fresh_index;
  z3::context & ctx;
  // The following encodes a cnf
  z3::expr_vector const & input; 

  z3::solver prop_solver;
  z3::solver theory_solver;
  
  // abstractions : (EUF + OCT) -> propositions
  z3::expr_map abstractions;
  // concretes = abstractions^{-1}
  z3::expr_map concretes;
  
  // The following encodes a cnf
  z3::expr_vector conflict_clauses;

  z3::expr abstract_atom(z3::expr const &);
  z3::expr abstract_lit(z3::expr const &);
  z3::expr abstract_clause(z3::expr const &);
  z3::expr_vector abstract_clauses(z3::expr_vector const &);

  z3::expr_vector mk_lits(z3::model const &);
  void block_conflict_clause(z3::expr_vector const &); 
  void loop();

  public:
  CDCL_T(z3::expr_vector const &);

  z3::expr_vector const getConflictClauses() const;

  std::ofstream & dimacsClause(std::ofstream &, z3::expr const &) const;
  void toDimacsFile() const;

  friend std::ostream & operator << (std::ostream &, CDCL_T const &);
};

#endif
