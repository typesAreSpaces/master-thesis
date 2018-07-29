#ifndef _HORN_CLAUSES_
#define _HORN_CLAUSES_

#include "HornClause.h"
#include <vector>

class HornClauses{
 private:
  static unsigned numHornClauses;
  std::vector<HornClause*> hornClauses;
 public:
  HornClauses();
  ~HornClauses();
  void addHornClause(UnionFind &, Vertex*, Vertex*, std::vector<Vertex*> &);
  void conditionalElimination();
  friend std::ostream & operator << (std::ostream &, HornClauses &);
};

#endif
