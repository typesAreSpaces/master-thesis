#ifndef _CONG_CLOSURE_E__
#define _CONG_CLOSURE_E__

#include "CongruenceClosure.h"

typedef std::vector<std::list<unsigned> > CCList;

class CongruenceClosureExplain : public CongruenceClosure {
  friend class Hornsat;
 public:
  CongruenceClosureExplain(const unsigned &, const z3::expr_vector &, CCList &, UnionFind &);
  void buildCongruenceClosure(std::list<unsigned> &);
  
  ~CongruenceClosureExplain();
  friend std::ostream & operator << (std::ostream &, const CongruenceClosureExplain &);
};


#endif
