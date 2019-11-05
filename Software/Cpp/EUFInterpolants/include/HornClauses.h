#ifndef _HORN_CLAUSES_
#define _HORN_CLAUSES_
#define notInSet(y, x) x.find(y) == x.end()

#include "HornClause.h"
#include "Terms.h"
#include <vector>
#include <set>
#include <map>

// Match1 : Uncommon Term -> Positions of Horn Clauses
typedef std::map<Term*, std::vector<unsigned> > Match1;
// Match2 : (Uncommon Term, Uncommon Term) -> Positions of Horn Clauses
typedef std::map<EquationTerm, std::vector<unsigned> > Match2;

typedef std::set<std::pair<unsigned, unsigned> > SetOfUnsignedPairs;

class HornClauses{
 public:
  HornClauses(CongruenceClosure &, CongruenceClosure &);
  ~HornClauses();
  
  // Adds a Horn clause using two terms of the form f(t_1, ..., t_n) and f(t'_1, ..., t'_n)
  void                     addHornClause(Term*, Term*,
					 bool);
  // Adds a Horn Clause using a vector of EquationTerms as antecedent
  // and an EquationTerm as conclusion
  void                     addHornClause(std::vector<EquationTerm> &, EquationTerm &,
					 bool);
  void                     conditionalElimination();
  unsigned                 size();
  std::vector<HornClause*> getHornClauses();
  std::vector<HornClause*> getReducibleHornClauses();
  friend std::ostream &    operator << (std::ostream &, const HornClauses &);
  std::ostream &           printMatch1(std::ostream &, Match1 &);
  std::ostream &           printMatch2(std::ostream &, Match2 &);
  
 private:
  std::vector<HornClause*>         horn_clauses;
  Match1                           mc1_antecedent, mc1_consequent;
  Match2                           mc2_antecedent, mc2_consequent;
  Match2                           reduced;
  std::map<EquationTerm, unsigned> reduced_length;
  CongruenceClosure &              original_cc;
  // Remainder: This auxiliar_cc must be reset
  // back to the original configuration after every
  // creation of new Horn Clause's
  CongruenceClosure &              auxiliar_cc;

  void decideHornClause(HornClause *, bool);
  void mergeType2_1AndType3(HornClause *, HornClause *, EquationTerm &);
  void mergeType2_1AndType4(HornClause *, HornClause *);
  void mergeType2AndType2(HornClause *, HornClause *);
  void mergeType2AndType3(HornClause *, HornClause *, Term *);
  void mergeType2AndType4(HornClause *, HornClause *);
  
  void simplifyHornClauses();
  void makeMatches(HornClause *, unsigned);
  void combinationHelper(HornClause *);
  void mc2ConsequentAndmc2Antecedent(SetOfUnsignedPairs &, bool &);
  void mc1ConsequentAndmc1Antecedent(SetOfUnsignedPairs &, bool &);
  void mc1ConsequentAndmc2Antecedent(SetOfUnsignedPairs &, bool &);
  void mc1ConsequentAndmc1Consequent(SetOfUnsignedPairs &, bool &);
  
  template<typename A>
    static void swap(std::vector<A> &, unsigned, unsigned);
  
  Term * getTerm(unsigned);
  Term * getTerm(Term *);
};

#endif
