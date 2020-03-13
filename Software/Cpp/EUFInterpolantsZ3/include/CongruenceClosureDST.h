#ifndef _CONG_CLOSUREDST__
#define _CONG_CLOSUREDST__

#include "CongruenceClosure.h"

class CongruenceClosureDST : public CongruenceClosure {
  friend class Hornsat;
 public:
  CongruenceClosureDST(const unsigned &, const z3::expr_vector &, PredList &, UnionFindExplain &);
  void buildCongruenceClosure(std::list<unsigned> &);
  ~CongruenceClosureDST();
  friend std::ostream & operator << (std::ostream &, const CongruenceClosureDST &);
};


#endif
