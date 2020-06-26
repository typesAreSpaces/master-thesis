#ifndef _CDCL_T_
#define _CDCL_T_
#define _DEBUG_CDCL_T_ 0

#include <iostream>
#include <z3++.h>
#include <map>

class CDCL_T {
  unsigned index;
  z3::context & ctx;

  z3::solver prop_solver;
  z3::solver theory_solver;
  
  z3::expr_map abstractions;
  z3::expr_map concretes;
  
  z3::expr_vector conflict_clauses;

  z3::expr abstract_atom(z3::expr const &);
  z3::expr abstract_lit(z3::expr const &);
  z3::expr abstract_clause(z3::expr const &);
  z3::expr_vector abstract_clauses(z3::expr_vector const &);

  z3::expr_vector mk_lits(z3::model const &);
  void block_conflict_clause(z3::expr_vector const &); 
  void loop();

  public:
  CDCL_T(z3::context &, z3::expr_vector const &);

  z3::expr_vector const getConflictClauses() const;

  friend std::ostream & operator << (std::ostream &, CDCL_T const &);
};

#endif
