#ifndef _EUF_INTERPOLANT_
#define _EUF_INTERPOLANT_

#include "CongruenceClosure.h"
#include "HornClauses.h"
#include "DisplayAST.h"
#include "z3++.h"
#include "ConvertReprToZ3.h"
#include <stack>
#include <map>
#include <set>

typedef std::map<std::string, std::set<unsigned> > symbolLocations;

class EUFInterpolant {
 private:
  CongruenceClosure    congruence_closure;
  Converter            cvt;
  std::vector<Term*> & terms;
  HornClauses          horn_clauses;
  z3::context &        ctx;
  symbolLocations      symbol_locations;
  equality             contradiction;
  void                 identifyCommonSymbols();
  void                 setCommonRepresentatives();
  void                 eliminationOfUncommonFSyms();
  void                 addNegativeHornClauses();
  z3::expr_vector   getUncommonTermsToElim(std::vector<HornClause*> &);
  z3::expr_vector   exponentialElimination(z3::expr_vector &,
					   z3::expr_vector &, z3::expr_vector &);
  z3::expr_vector   substitutions(z3::expr &, z3::expr &, z3::expr_vector &);
   
 public:
  EUFInterpolant(z3::context &, const z3::expr &, Converter &);
  EUFInterpolant(z3::context &, const z3::expr &, std::set<std::string> &, Converter &);
  ~EUFInterpolant();
  void                     test();
  z3::expr                 algorithm();
  std::vector<HornClause*> getHornClauses();
  friend std::ostream &    operator << (std::ostream &, EUFInterpolant &);
};

#endif
