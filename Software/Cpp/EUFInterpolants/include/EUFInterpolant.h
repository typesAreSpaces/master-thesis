#ifndef _EUF_INTERPOLANT_
#define _EUF_INTERPOLANT_

#include "CongruenceClosure.h"

class EUFInterpolant {
 private:
  CongruenceClosure & cc;
 public:
  EUFInterpolant(CongruenceClosure &);
  ~EUFInterpolant();
  void algorithm();
  std::ostream & print(std::ostream &);
};

#endif
