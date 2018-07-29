#ifndef _HORN_CLAUSE_
#define _HORN_CLAUSE_

#include "UnionFind.h"
#include "Vertex.h"
#include <set>
#include <vector>
#include <utility>

typedef std::pair<Vertex*, Vertex*> equality;

class HornClause{
 private:
  UnionFind localUF;
  std::set<equality> antecedent;
  equality consequent;
 public:
  HornClause(UnionFind &, Vertex*, Vertex*, std::vector<Vertex*> &);
  ~HornClause();
  void normalize();
  bool checkTrivial();
  friend std::ostream & operator << (std::ostream &, HornClause &);
};

#endif
