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
  CongruenceClosure      congruence_closure;
  Converter              cvt;
  std::vector<Vertex*> & terms;
  HornClauses            horn_clauses;
  Z3_context             ctx;
  symbolLocations        symbol_locations;
  equality               contradiction;
  void                   identifyCommonSymbols();
  void                   setCommonRepresentatives();
  void                   eliminationOfUncommonFSyms();
  void                   addNegativeHornClauses();
  std::set<unsigned>     getUncommonTermsToElim(std::vector<HornClause*> &);
  z3::expr_vector        exponentialElimination(z3::expr_vector &,
												std::set<unsigned> &, z3::expr_vector &);
  z3::expr_vector        substitutions(z3::expr &, z3::expr &, z3::expr_vector &);
   
 public:
  EUFInterpolant(Z3_context, Z3_ast, Converter &);
  EUFInterpolant(Z3_context, Z3_ast, std::set<std::string> &, Converter &);
  ~EUFInterpolant();
  std::vector<HornClause*> getHornClauses();
  z3::expr                 algorithm();
  friend std::ostream &    operator << (std::ostream &, EUFInterpolant &);
};

#endif
