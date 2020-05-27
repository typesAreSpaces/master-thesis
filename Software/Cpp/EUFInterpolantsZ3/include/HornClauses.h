#ifndef _HORN_CLAUSES_
#define _HORN_CLAUSES_
#include <unordered_map>
#define notInSet(y, x) x.find(y) == x.end()
#define DEBUG_HORN_CLAUSES       0
#define DEBUG_ADDINGHC           0
#define DEBUG_MAKE_MATCHES       0
#define DEBUG_CE                 0
#define DEBUG_COMBINATION_HELPER 0
#define DEBUG_MATCHES            0
#define DEBUG_DESTRUCTOR_HCS     0

#include "Z3Subterms.h"
#include "HornClause.h"
#include "Match.h"
#include "Replacement.h"

class HornClauses {

  UnionFindExplain &                         ufe;
  std::unordered_map<unsigned, HornClause *> horn_clauses;
  unsigned                                   curr_num_horn_clauses;
  unsigned                                   max_lit_id;

  void simplifyHornClauses(); // TODO: Implement this
  
 public:
  HornClauses(UnionFindExplain &);
  ~HornClauses();
  void swapHornClauses(unsigned, unsigned);
  void add(HornClause *);


  unsigned                       size() const;
  HornClause *                   operator[] (unsigned) const; 
  std::vector<HornClause*> const getHornClauses() const;
  unsigned                       getUFESize()  const;
  unsigned                       getMaxLitId() const;
  friend std::ostream &          operator << (std::ostream &, const HornClauses &);
};

#endif
