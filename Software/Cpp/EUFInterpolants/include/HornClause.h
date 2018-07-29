#ifndef _HORN_CLAUSE_
#define _HORN_CLAUSE_

#include "UnionFind.h"
#include "Vertex.h"
#include <set>
#include <utility>

typedef std::pair<unsigned, unsigned> equality;

class HornClause{
 private:
  UnionFind localUF;
  std::set<equality> antecedent;
  equality consequent;
 public:
  HornClause(UnionFind &, Vertex*, Vertex*);
  ~HornClause();
  void normalize();
  bool checkTrivial();
  friend std::ostream & operator << (std::ostream &, HornClause &);
};

#endif
