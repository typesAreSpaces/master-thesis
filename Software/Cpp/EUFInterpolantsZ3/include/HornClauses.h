#ifndef _HORN_CLAUSES_
#define _HORN_CLAUSES_

#include <set>
#include "HornClause.h"

// Match1 : Uncommon term (indexed by its id) -> Positions of Horn Clauses
typedef std::vector<std::vector<unsigned> >      Match1;
// Match2 : Uncommon equation (indexed by its id) -> Positions of Horn Clauses
typedef std::vector<std::vector<unsigned> >      Match2;
typedef std::set<std::pair<unsigned, unsigned> > SetOfUnsignedPairs;

class HornClauses {

  z3::context &                    ctx;
  std::vector<HornClause *>        horn_clauses;
  Match1                           mc1_antecedent, mc1_consequent;
  Match2                           mc2_antecedent, mc2_consequent;
  unsigned                         _size;
  unsigned                         curr_num_horn_clauses = 0;
  // Match2                           reduced;
  // std::map<EquationTerm, unsigned> reduced_length;

  void makeMatches(HornClause *, unsigned);
  // void combinationHelper(HornClause *);
  // void simplifyHornClauses();

  // void mergeType2_1AndType3(HornClause *, HornClause *, EquationTerm &);
  // void mergeType2_1AndType4(HornClause *, HornClause *);
  // void mergeType2AndType2(HornClause *, HornClause *, Term *);
  // void mergeType2AndType3(HornClause *, HornClause *, Term *);
  // void mergeType2AndType4(HornClause *, HornClause *);
  
  // void mc2ConsequentAndmc2Antecedent(SetOfUnsignedPairs &, bool &); 
  // void mc1ConsequentAndmc1Antecedent(SetOfUnsignedPairs &, bool &);
  // void mc1ConsequentAndmc2Antecedent(SetOfUnsignedPairs &, bool &);
  // void mc1ConsequentAndmc1Consequent(SetOfUnsignedPairs &, bool &);
  
  // template<typename A>
  // static void swap(std::vector<A> &, unsigned, unsigned);
  
 public:
  HornClauses(z3::context &, unsigned);
  ~HornClauses();

  void add(HornClause *);
  // void                       conditionalElimination();             // TODO:
  unsigned                   size();
  std::vector<HornClause*> & getHornClauses();
  // void                       getTermsToReplace(z3::expr_vector &); // TODO:
  // std::vector<HornClause*>   getReducibleHornClauses();
  // std::ostream &             printMatch1(std::ostream &, Match1 &);
  // std::ostream &             printMatch2(std::ostream &, Match2 &);
  friend std::ostream &      operator << (std::ostream &, const HornClauses &);
};

#endif
