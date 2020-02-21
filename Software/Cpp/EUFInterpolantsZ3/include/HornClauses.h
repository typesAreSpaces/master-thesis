#ifndef _HORN_CLAUSES_
#define _HORN_CLAUSES_
#define notInSet(y, x) x.find(y) == x.end()

#include <set>
#include "HornClause.h"
#include "Match.h"

typedef std::set<std::pair<unsigned, unsigned> > SetOfUnsignedPairs;

class HornClauses {

  z3::context &             ctx;
  std::vector<HornClause *> horn_clauses;
  Match                     mc1_antecedent, mc1_consequent;
  Match                     mc2_antecedent, mc2_consequent;
  unsigned                  curr_num_horn_clauses = 0;
  // Match2                           reduced;
  // std::map<EquationTerm, unsigned> reduced_length;

  void makeMatches(HornClause *, unsigned);
  // void combinationHelper(HornClause *);
  void simplifyHornClauses(); // TODO: NEXT NEXT NEXT

  // void mergeType2_1AndType3(HornClause *, HornClause *, EquationTerm &);
  // void mergeType2_1AndType4(HornClause *, HornClause *);
  // void mergeType2AndType2(HornClause *, HornClause *, Term *);
  // void mergeType2AndType3(HornClause *, HornClause *, Term *);
  // void mergeType2AndType4(HornClause *, HornClause *);
  
  void mc2ConsequentAndmc2Antecedent(SetOfUnsignedPairs &, bool &); // TODO: NEXT NEXT
  void mc1ConsequentAndmc1Antecedent(SetOfUnsignedPairs &, bool &); // TODO: NEXT NEXT
  void mc1ConsequentAndmc2Antecedent(SetOfUnsignedPairs &, bool &); // TODO: NEXT NEXT
  void mc1ConsequentAndmc1Consequent(SetOfUnsignedPairs &, bool &); // TODO: NEXT NEXT
  
  // template<typename A>
  // static void swap(std::vector<A> &, unsigned, unsigned);
  
 public:
  HornClauses(z3::context &);
  ~HornClauses();

  void add(HornClause *);
  void                       conditionalElimination();                // TODO: NEXT
  unsigned                   size();
  std::vector<HornClause*> & getHornClauses();
  HornClause*                operator[] (unsigned);
  // void                       getTermsToReplace(z3::expr_vector &); // TODO:
  // std::vector<HornClause*>   getReducibleHornClauses();
  friend std::ostream &      operator << (std::ostream &, const HornClauses &);
};

#endif
