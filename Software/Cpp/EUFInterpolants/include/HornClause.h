#ifndef _HORN_CLAUSE_
#define _HORN_CLAUSE_

#include "UnionFind.h"
#include "Vertex.h"
#include <vector>
#include <utility>

typedef std::pair<Vertex*, Vertex*> equality;

class HornClause{
 private:
  UnionFind localUF;
  std::vector<equality> antecedent;
  equality consequent;
  bool antecedentQ, consequentQ;
 public:
  HornClause(UnionFind &, Vertex*, Vertex*, std::vector<Vertex*> &);
  ~HornClause();
  void normalize();
  bool checkTrivial();
  bool getAntecedentQ();
  bool getConsequentQ();
  bool getMaximalConsequentQ();
  std::vector<equality> & getAntecedent();
  equality & getConsequent();
  UnionFind & getLocalUF();
  friend std::ostream & operator << (std::ostream &, HornClause &);
};

#endif
