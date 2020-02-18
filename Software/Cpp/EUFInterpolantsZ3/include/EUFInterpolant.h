#ifndef _EUF_INTERPOLANT_
#define _EUF_INTERPOLANT_

#include "HornClauses.h"

class EUFInterpolant {

  HornClauses       horn_clauses;
  
  void              eliminationOfUncommonFSyms();
  void              addNegativeHornClauses();
  z3::expr_vector   getUncommonTermsToElim(std::vector<HornClause*> &);
  z3::expr_vector   exponentialElimination(z3::expr_vector &, z3::expr_vector &, z3::expr_vector &);
  z3::expr_vector   substitutions(z3::expr &, z3::expr &, z3::expr_vector &);
  
 public:
  EUFInterpolant(const z3::expr &);
  EUFInterpolant(const z3::expr &, const z3::expr &);
  ~EUFInterpolant();
  z3::expr                 buildInterpolant();
  friend std::ostream &    operator << (std::ostream &, const EUFInterpolant &);
};

#endif
