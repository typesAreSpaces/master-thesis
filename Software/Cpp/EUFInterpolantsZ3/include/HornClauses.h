#ifndef _HORN_CLAUSES_
#define _HORN_CLAUSES_
#define notInSet(y, x) x.find(y) == x.end()

#include <set>
#include "HornClause.h"
#include "Match.h"
#include "Replacement.h"

typedef std::set<std::pair<unsigned, unsigned> > SetOfUnsignedPairs;

class HornClauses {

  z3::context &             ctx;
  const z3::expr_vector &   subterms;
  std::vector<HornClause *> horn_clauses;
  unsigned                  curr_num_horn_clauses = 0;
  // Match2                           reduced;
  // std::map<EquationTerm, unsigned> reduced_length;

  // void combinationHelper(HornClause *);
  void simplifyHornClauses();                                                               // TODO: NEXT NEXT 
  
  // template<typename A>
  // static void swap(std::vector<A> &, unsigned, unsigned);
  
 public:
  HornClauses(z3::context &, const z3::expr_vector &);
  ~HornClauses();

  void                             add(HornClause *);
  void                             conditionalElimination(std::vector<Replacement>); // TODO: NEXT // KEEP WORKING HERE
  unsigned                         size() const;
  unsigned                         maxID() const;
  const std::vector<HornClause*> & getHornClauses() const;
  HornClause *                     operator[] (unsigned);
  const z3::expr_vector &          getSubterms() const;
  // void                       getTermsToReplace(z3::expr_vector &);                       // TODO:
  // std::vector<HornClause*>   getReducibleHornClauses();
  friend std::ostream &            operator << (std::ostream &, const HornClauses &);
};

#endif
