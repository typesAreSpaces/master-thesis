#ifndef _EUF_INTERPOLANT_
#define _EUF_INTERPOLANT_

#include "CongruenceClosure.h"
#include "HornClauses.h"
#include "displayAST.h"
#include <stack>
#include <map>
#include <set>

typedef std::map<std::string, std::set<unsigned> > symbolLoc;

class EUFInterpolant {
 private:
  CongruenceClosure cc;
  HornClauses hC;
	Z3_context ctx;
  void identifyCommonSymbols();
  void setCommonRepresentatives();
  void eliminationOfUncommonFSyms();
  symbolLoc symbolPos;
 public:
  EUFInterpolant(Z3_context, Z3_ast);
  EUFInterpolant(Z3_context, Z3_ast, std::set<std::string> &);
  ~EUFInterpolant();
  void algorithm();
  std::ostream & print(std::ostream &);
};

#endif
