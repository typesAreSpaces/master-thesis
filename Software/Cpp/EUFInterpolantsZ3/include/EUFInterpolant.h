#ifndef _EUF_INTERPOLANT_
#define _EUF_INTERPOLANT_

#include <map>
#include "HornClauses.h"

typedef std::map<std::string, std::vector<unsigned> > UncommonPositions;

class EUFInterpolant {

  HornClauses       horn_clauses;
  std::vector<bool> visited;
  z3::expr_vector   subterms;
  UncommonPositions uncommon_positions;

  void              init(z3::expr const &);
  void              eliminationOfUncommonFSyms(); 
  z3::expr_vector   getUncommonTermsToElim(std::vector<HornClause*> &); // (?) ----------------------------
  z3::expr_vector   exponentialElimination(z3::expr_vector &, z3::expr_vector &, z3::expr_vector &); // <-|
  z3::expr_vector   substitutions(z3::expr &, z3::expr &, z3::expr_vector &);
  
 public:
  EUFInterpolant(z3::expr const &);
  ~EUFInterpolant();
  void                  buildInterpolant();
  friend std::ostream & operator << (std::ostream &, const EUFInterpolant &);
};

#endif
