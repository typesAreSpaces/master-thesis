#ifndef _HORN_CLAUSES_
#define _HORN_CLAUSES_
#define notInSet(y, x) x.find(y) == x.end()

#include <set>
#include "Z3Subterms.h"
#include "HornClause.h"
#include "Match.h"
#include "Replacement.h"

typedef std::set<std::pair<unsigned, unsigned> > SetOfUnsignedPairs;

class HornClauses {

  z3::context &             ctx;
  Z3Subterms &              subterms;
  std::vector<HornClause *> horn_clauses;
  unsigned                  curr_num_horn_clauses = 0;
  // Match2                           reduced;
  // std::map<EquationTerm, unsigned> reduced_length;

  void simplifyHornClauses();                                                               // TODO: NEXT NEXT 
  
  // template<typename A>
  // static void swap(std::vector<A> &, unsigned, unsigned);
  
 public:
  HornClauses(z3::context &, Z3Subterms &);
  ~HornClauses();

  void                             add(HornClause *);
  void                             conditionalElimination(std::vector<Replacement>);         // TODO: NEXT // KEEP WORKING HERE
  unsigned                         size() const;
  const std::vector<HornClause*> & getHornClauses() const;
  HornClause *                     operator[] (unsigned);
  const Z3Subterms &               getSubterms() const;
  // void                       getTermsToReplace(z3::expr_vector &);                       // TODO:
  // std::vector<HornClause*>   getReducibleHornClauses();
  friend std::ostream &            operator << (std::ostream &, const HornClauses &);
};

#endif
