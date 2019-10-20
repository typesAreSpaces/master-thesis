#ifndef _EUF_INTERPOLANT_
#define _EUF_INTERPOLANT_

#include "CongruenceClosure.h"
#include "HornClauses.h"
#include "ConvertReprToZ3.h"
#include <map>
#include <set>

class EUFInterpolant {
 public:
  EUFInterpolant(const z3::expr &, const z3::sort &);
  EUFInterpolant(const z3::expr &, const UncommonSymbols &, const z3::sort &);
  ~EUFInterpolant();
  void                     test();
  z3::expr                 buildInterpolant();
  std::vector<HornClause*> getHornClauses();
  friend std::ostream &    operator << (std::ostream &, EUFInterpolant &);
 private:
  CongruenceClosure auxiliar_closure;
  CongruenceClosure original_closure;
  Converter         cvt;
  HornClauses       horn_clauses;
  EquationTerm      contradiction;
  
  void              eliminationOfUncommonFSyms();
  void              addNegativeHornClauses();
  z3::expr_vector   getUncommonTermsToElim(std::vector<HornClause*> &);
  z3::expr_vector   exponentialElimination(z3::expr_vector &, z3::expr_vector &, z3::expr_vector &);
  z3::expr_vector   substitutions(z3::expr &, z3::expr &, z3::expr_vector &);
};

#endif
