#ifndef _HORN_CLAUSE_
#define _HORN_CLAUSE_

#include "UnionFind.h"
#include "Vertex.h"
#include <vector>
#include <utility>

typedef std::pair<Vertex*, Vertex*> equality;

class HornClause{
 private:
	static UnionFind globalUF;
	static bool change;
	UnionFind localUF;
  std::vector<equality> antecedent;
  equality consequent;
  bool antecedentQ, consequentQ;
 public:
  HornClause(UnionFind &, std::vector<equality> &, equality &, std::vector<Vertex*> &);
  HornClause(UnionFind &, Vertex*, Vertex*, std::vector<Vertex*> &, bool);
  ~HornClause();
  void normalize();
  bool checkTrivial();
  bool getAntecedentQ();
  bool getConsequentQ();
  bool getMaximalConsequentQ();
  std::vector<equality> & getAntecedent();
  equality & getConsequent();
  UnionFind & getLocalUF();
	static UnionFind & getGlobalUF();
  friend std::ostream & operator << (std::ostream &, HornClause &);
	friend bool operator <(HornClause &, HornClause &);
	friend bool operator >(HornClause &, HornClause &);
};

#endif
