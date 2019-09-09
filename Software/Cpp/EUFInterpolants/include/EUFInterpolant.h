#ifndef _EUF_INTERPOLANT_
#define _EUF_INTERPOLANT_

#include "CongruenceClosure.h"
#include "HornClauses.h"
#include "ConvertReprToZ3.h"
#include <stack>
#include <map>
#include <set>

typedef std::map<std::string, std::set<unsigned> > SymbolLocations;

class EUFInterpolant {
 public:
  EUFInterpolant(z3::context &, const z3::expr &, const z3::sort &);
  EUFInterpolant(z3::context &, const z3::expr &, std::set<std::string> &, const z3::sort &);
  ~EUFInterpolant();
  void                     test();
  z3::expr                 buildInterpolant();
  std::vector<HornClause*> getHornClauses();
  friend std::ostream &    operator << (std::ostream &, EUFInterpolant &);
 private:
  CongruenceClosure    congruence_closure;
  Converter            cvt;
  HornClauses          horn_clauses;
  z3::context &        ctx;
  SymbolLocations      symbol_locations;
  EquationTerm         contradiction;
  void                 identifyCommonSymbols();
  void                 setCommonRepresentatives();
  void                 eliminationOfUncommonFSyms();
  void                 addNegativeHornClauses();
  z3::expr_vector      getUncommonTermsToElim(std::vector<HornClause*> &);
  z3::expr_vector      exponentialElimination(z3::expr_vector &, z3::expr_vector &, z3::expr_vector &);
  z3::expr_vector      substitutions(z3::expr &, z3::expr &, z3::expr_vector &);
};

#endif
