#ifndef _HORN_CLAUSES_
#define _HORN_CLAUSES_
#define existential(x, y) x.find(y) == x.end()

#include "HornClause.h"
#include "Terms.h"
#include <vector>
#include <set>
#include <map>

// match1 : Uncommon Vertex -> Positions of Horn Clauses
typedef std::map<Vertex*, std::vector<unsigned> > match1;
// match2 : (Uncommon Vertex, Uncommon Vertex) -> Positions of Horn Clauses
typedef std::map<equality, std::vector<unsigned> > match2;

typedef std::set<std::pair<unsigned, unsigned> > SetOfUnsignedPairs;

class HornClauses{
 private:
  static unsigned               num_horn_clauses;
  std::vector<HornClause*>      horn_clauses;
  match1                        mc1_antecedent, mc1_consequent;
  match2                        mc2_antecedent, mc2_consequent;
  match2                        reduced;
  std::map<equality, unsigned>  reduced_length;
  std::vector<Vertex*> &        local_terms;
  void mergeType2_1AndType3(HornClause *, HornClause *);
  void mergeType2_1AndType4(HornClause *, HornClause *);
  void mergeType2AndType2(HornClause *, HornClause *);
  void mergeType2AndType3(HornClause *, HornClause *);
  void mergeType2AndType4(HornClause *, HornClause *);
  void simplify();
  void makeMatches(HornClause *, unsigned);
  void combinationHelper(HornClause *);
  void orient(HornClause *);
  void mc2ConsequentAndmc2Antecedent(SetOfUnsignedPairs &, bool &);
  void mc1ConsequentAndmc1Antecedent(SetOfUnsignedPairs &, bool &);
  void mc1ConsequentAndmc2Antecedent(SetOfUnsignedPairs &, bool &);
  void mc1ConsequentAndmc1Antecedent2(SetOfUnsignedPairs &, bool &);
  template<typename A>
	static void swap(std::vector<A> &, unsigned, unsigned);
  Vertex * getVertex(unsigned);
  Vertex * getVertex(Vertex *);
	
 public:
  HornClauses(std::vector<Vertex*> &);
  ~HornClauses();
  void addHornClause(UnionFind &, Vertex*, Vertex*, bool);
  void addHornClause(UnionFind &, std::vector<equality> &, equality &, bool);
  void conditionalElimination();
  unsigned size();
  std::vector<HornClause*> getHornClauses();
  std::vector<HornClause*> getReducibleHornClauses();
  friend std::ostream & operator << (std::ostream &, HornClauses &);
  std::ostream & printMatch1(std::ostream &, match1 &);
  std::ostream & printMatch2(std::ostream &, match2 &);
};

#endif
