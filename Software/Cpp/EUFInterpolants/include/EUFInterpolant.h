#ifndef _EUF_INTERPOLANT_
#define _EUF_INTERPOLANT_

#include "CongruenceClosure.h"

class EUFInterpolant {
 private:
  CongruenceClosure & cc;
 public:
  EUFInterpolant();
  ~EUFInterpolant();
  void algorithm();
  void print(std::ostream &);
};

#endif
