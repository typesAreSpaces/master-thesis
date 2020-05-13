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

  UnionFindExplain &        ufe;
  std::vector<HornClause *> horn_clauses;
  unsigned                  curr_num_horn_clauses = 0;

  void simplifyHornClauses(); // TODO: NEXT NEXT 
  
 public:
  HornClauses(UnionFindExplain &);
  ~HornClauses();

  void                             add(HornClause *);
  void                             conditionalElimination(std::vector<Replacement>);         // TODO: NEXT // KEEP WORKING HERE
  unsigned                         size() const;
  const std::vector<HornClause*> & getHornClauses() const;
  HornClause *                     operator[] (unsigned);
  // void                       getTermsToReplace(z3::expr_vector &);                       // TODO:
  // std::vector<HornClause*>   getReducibleHornClauses();
  friend std::ostream &            operator << (std::ostream &, const HornClauses &);
};

#endif
