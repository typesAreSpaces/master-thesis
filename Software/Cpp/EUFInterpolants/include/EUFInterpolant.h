#ifndef _EUF_INTERPOLANT_
#define _EUF_INTERPOLANT_

#include "CongruenceClosure.h"
#include "HornClauses.h"
#include "DisplayAST.h"
#include <stack>
#include <map>
#include <set>

typedef std::map<std::string, std::set<unsigned> > symbolLocations;

class EUFInterpolant {
 private:
  CongruenceClosure congruence_closure;
  HornClauses       horn_clauses;
  Z3_context        ctx;
  symbolLocations   symbol_locations;
  void identifyCommonSymbols();
  void setCommonRepresentatives();
  void eliminationOfUncommonFSyms();
  void addNegativeHornClauses();
  
 public:
  EUFInterpolant(Z3_context, Z3_ast);
  EUFInterpolant(Z3_context, Z3_ast, std::set<std::string> &);
  ~EUFInterpolant();
  std::vector<HornClause*> getHornClauses();
  void algorithm();
  friend std::ostream & operator << (std::ostream &, EUFInterpolant &);
};

#endif
