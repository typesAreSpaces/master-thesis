#ifndef _EUF_INTERPOLANT_
#define _EUF_INTERPOLANT_

#include "CongruenceClosure.h"
#include <stack>
#include <map>
#include <set>

class EUFInterpolant {
 private:
  CongruenceClosure cc;
  void identifyCommonSymbols();
  void setCommonRepresentatives();
  void eliminationOfUncommonFSyms();
  std::map<std::string, std::set<int> > symbolPos;
 public:
  EUFInterpolant(Z3_context, Z3_ast);
  EUFInterpolant(Z3_context, Z3_ast, std::set<std::string> &);
  ~EUFInterpolant();
  void algorithm();
  std::ostream & print(std::ostream &);
};

#endif
