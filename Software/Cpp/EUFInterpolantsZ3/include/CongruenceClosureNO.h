#ifndef _CONG_CLOSURENO__
#define _CONG_CLOSURENO_

#include "CongruenceClosure.h"

typedef std::vector<std::list<unsigned> > CCList;

class CongruenceClosureNO : public CongruenceClosure {
  friend class Hornsat;
 public:
  CongruenceClosureNO(const unsigned &, const z3::expr_vector &, CCList &, UnionFind &);
  void buildCongruenceClosure(std::list<unsigned> &);
  ~CongruenceClosureNO();
  friend std::ostream & operator << (std::ostream &, const CongruenceClosureNO &);
};


#endif
