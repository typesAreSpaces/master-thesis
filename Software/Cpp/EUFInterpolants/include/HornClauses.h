#ifndef _HORN_CLAUSES_
#define _HORN_CLAUSES_

#include "HornClause.h"
#include "Vertex.h"
#include <vector>
#include <set>
#include <map>

extern bool debugHornClauses;

// match1 : Uncommon Vertex -> Positions of Horn Clauses
typedef std::map<Vertex*, std::vector<unsigned> > match1;
// match2 : (Uncommon Vertex, Uncommon Vertex) -> Positions of Horn Clauses
typedef std::map<equality, std::vector<unsigned> > match2;

class HornClauses{
 private:
  static unsigned numHornClauses;
  std::vector<HornClause*> hornClauses;
  match1 mc1A, mc1C;
  match2 mc2A, mc2C;
	match2 rewriting;
  std::vector<Vertex*> & localTerms;
  void mergeType2_1AndType3(HornClause *, HornClause *);
  void mergeType2_1AndType4(HornClause *, HornClause *);
  void mergeType2AndType2(HornClause *, HornClause *);
  void mergeType2AndType3(HornClause *, HornClause *);
  void mergeType2AndType4(HornClause *, HornClause *);
	void rewrite();
  void makeMatches(HornClause * hc, unsigned);
	void combinationHelper(HornClause *);
	void orient(HornClause *);
 public:
  HornClauses(std::vector<Vertex*> &);
  ~HornClauses();
  void addHornClause(UnionFind &, Vertex*, Vertex*);
  void conditionalElimination();
	unsigned size();
  friend std::ostream & operator << (std::ostream &, HornClauses &);
	std::ostream & printMatch1(std::ostream &, match1 &);
	std::ostream & printMatch2(std::ostream &, match2 &);
};

#endif
