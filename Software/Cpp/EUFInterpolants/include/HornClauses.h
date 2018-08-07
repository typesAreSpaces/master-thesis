#ifndef _HORN_CLAUSES_
#define _HORN_CLAUSES_

#include "HornClause.h"
#include "Vertex.h"
#include <vector>
#include <set>
#include <map>

// match1 : Uncommon Vertex -> Positions of Horn Clauses
typedef std::map<Vertex*, std::vector<unsigned> > match1;
// match1 : (Uncommon Vertex, Uncommon Vertex) -> Positions of Horn Clauses
typedef std::map<equality, std::vector<unsigned> > match2;

class HornClauses{
 private:
  static unsigned numHornClauses;
  std::vector<HornClause*> hornClausesType1;
  std::vector<HornClause*> hornClausesType2;
  std::vector<HornClause*> hornClausesType2_1;
  std::vector<HornClause*> hornClausesType3;
  std::vector<HornClause*> hornClausesType4;
  match1 mc1A, mc1C;
  match2 mc2A, mc2C;
 public:
  HornClauses();
  ~HornClauses();
  void addHornClause(UnionFind &, Vertex*, Vertex*, std::vector<Vertex*> &);
  void dependencyAnalysis();
  void conditionalElimination();
  void makeMatches(HornClause * hc, unsigned);
  friend std::ostream & operator << (std::ostream &, HornClauses &);
};

#endif
