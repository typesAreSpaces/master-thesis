#ifndef _HORN_CLAUSES_
#define _HORN_CLAUSES_

#include "HornClause.h"
#include <vector>

class HornClauses{
 private:
  static unsigned numHornClauses;
  std::vector<HornClause*> hornClausesType1;
  std::vector<HornClause*> hornClausesType2;
  std::vector<HornClause*> hornClausesType3;
  std::vector<HornClause*> hornClausesType4;
 public:
  HornClauses();
  ~HornClauses();
  void addHornClause(UnionFind &, Vertex*, Vertex*, std::vector<Vertex*> &);
  void dependencyAnalysis();
  void conditionalElimination();
  friend std::ostream & operator << (std::ostream &, HornClauses &);
};

#endif
