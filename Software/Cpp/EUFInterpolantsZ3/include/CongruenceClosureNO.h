#ifndef _CONG_CLOSURENO__
#define _CONG_CLOSURENO__

#include "CongruenceClosure.h"

class CongruenceClosureNO : public CongruenceClosure {
  friend class Hornsat;
 public:
  CongruenceClosureNO(const unsigned &, const z3::expr_vector &, PredList &, UnionFindExplain &);
  void buildCongruenceClosure(std::list<unsigned> &);
  void combine(unsigned, unsigned);
  bool areCongruent(unsigned, unsigned);
  ~CongruenceClosureNO();
  friend std::ostream & operator << (std::ostream &, const CongruenceClosureNO &);
};


#endif
