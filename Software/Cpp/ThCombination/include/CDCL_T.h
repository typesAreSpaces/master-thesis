#ifndef _CDCL_T_
#define _CDCL_T_
#define _DEBUG_CDCL_T_ 0
#define PREFIX_PROP "c__p_"
#define PREFIX_PROP_LIT(literal) ctx.bool_const((PREFIX_PROP + std::to_string(literal)).c_str())
// PREFIX_PROP_LEN is the length of PREFIX_PROP
#define PREFIX_PROP_LEN 5
#define PROP2LIT(name) (unsigned)std::stol(name.substr(PREFIX_PROP_LEN, name.size() - 1))

#include <iostream>
#include <fstream>
#include <z3++.h>
#include <stdlib.h>
#include <string.h>
#include "Theories.h"

class CDCL_setup { 
};

class CDCL_T {

  unsigned abstraction_fresh_index;
  z3::context & ctx;
  // The following encodes a cnf
  z3::expr_vector const & input; 

  // abstractions : (EUF + OCT) -> propositions
  z3::expr_map abstractions;
  // concretes = abstractions^{-1}
  z3::expr_map concretes;
  
  // The following encodes a cnf
  z3::expr_vector abstract_conflict_clauses;

  //z3::solver prop_solver;
  z3::solver theory_solver;

  z3::expr abstract_atom(z3::expr const &);
  z3::expr abstract_lit(z3::expr const &);
  z3::expr abstract_clause(z3::expr const &);
  z3::expr_vector abstract_clauses(z3::expr_vector const &);

  z3::expr_vector mk_lits(z3::model const &);
  void loop();

  public:
  CDCL_T(z3::expr_vector const &);

  z3::expr_vector const getConflictClauses() const;

  std::ofstream & dimacsLit(std::ofstream &, z3::expr const &);
  std::ofstream & dimacsClause(std::ofstream &, z3::expr const &);
  void toDimacsFile();

  z3::expr concretizeAbstraction(int);

  friend std::ostream & operator << (std::ostream &, CDCL_T const &);
};

#endif
