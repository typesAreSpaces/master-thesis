#ifndef _EUF_INTERPOLANT_
#define _EUF_INTERPOLANT_

#include "CongruenceClosure.h"
#include <stack>

class EUFInterpolant {
 private:
  CongruenceClosure cc;
  void identifyCommonSymbols();
 public:
  EUFInterpolant(Z3_context, Z3_ast);
  EUFInterpolant(Z3_context, Z3_ast, std::set<std::string> &);
  ~EUFInterpolant();
  void algorithm();
  std::ostream & print(std::ostream &);
};

#endif
