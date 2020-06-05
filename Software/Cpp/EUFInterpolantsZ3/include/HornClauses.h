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
#include "Replacement.h"

typedef std::unordered_map<unsigned, HornClause *> UnordMapHornClauses;

class HornClauses {

  UnionFindExplain &                         ufe;
  UnordMapHornClauses horn_clauses;
  unsigned                                   curr_num_horn_clauses;
  unsigned                                   max_lit_id;

  void simplifyHornClauses(); // TODO: Implement this
  
 public:
  HornClauses(UnionFindExplain &);
  ~HornClauses();
  void swapHornClauses(unsigned, unsigned);
  void add(HornClause *);

  class iterator {
    UnordMapHornClauses::iterator it;
    public:
      iterator(UnordMapHornClauses::iterator it) : 
        it(it) {}
      bool operator ==(iterator const & other){
        return it == other.it;
      }
      bool operator !=(iterator const & other){
        return it != other.it;
      }
      iterator & operator ++(){
        ++it;
        return *this;
      }
      HornClause const * operator *() const {
        return it->second;
      }
  };

  iterator begin() {
    return iterator(this->horn_clauses.begin());
  }
  iterator end() {
    return iterator(this->horn_clauses.end());
  }

  unsigned                       size() const;
  HornClause *                   operator[] (unsigned) const; 
  std::vector<HornClause*> const getHornClauses() const;
  unsigned                       getUFESize()  const;
  unsigned                       getMaxLitId() const;
  friend std::ostream &          operator << (std::ostream &, const HornClauses &);
};

#endif
