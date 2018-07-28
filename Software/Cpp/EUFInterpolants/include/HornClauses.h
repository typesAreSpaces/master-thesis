#ifndef _HORN_CLAUSES_
#define _HORN_CLAUSES_
#endif

#include "HornClause.h"
#include <vector>

class HornClauses{
 private:
  std::vector<HornClause*> clauses;
 public:
  HornClauses();
  ~HornClauses();
};
