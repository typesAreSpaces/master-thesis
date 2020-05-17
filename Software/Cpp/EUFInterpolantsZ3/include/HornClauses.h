#ifndef _HORN_CLAUSES_
#define _HORN_CLAUSES_
#include <unordered_map>
#define notInSet(y, x) x.find(y) == x.end()

#include "Z3Subterms.h"
#include "HornClause.h"
#include "Match.h"
#include "Replacement.h"

class HornClauses {

  UnionFindExplain &                         ufe;
  std::unordered_map<unsigned, HornClause *> horn_clauses;
  unsigned                                   curr_num_horn_clauses = 0;

  void simplifyHornClauses(); // TODO: Implement this
  
 public:
  HornClauses(UnionFindExplain &);
  ~HornClauses();
  void                  swapHornClauses(unsigned, unsigned);
  void                  add(HornClause *);
  void                  conditionalElimination(std::vector<Replacement>); // TODO: Implement this
  unsigned                       size() const;
  HornClause *                   operator[] (unsigned) const; 
  std::vector<HornClause*> const getHornClauses() const;
  friend std::ostream &          operator << (std::ostream &, const HornClauses &);
};

#endif
