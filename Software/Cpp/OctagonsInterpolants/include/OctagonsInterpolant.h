#ifndef _OCTAGONSINTER_
#define _OCTAGONSINTER_
#define DEBUG_OCT_INTER_ false

#include <iostream>
#include <vector>
#include "Octagon.h"

typedef std::vector<int> vi;

class OctagonsInterpolant{
 private:
  vi inequalities, variablesToEliminate;
  std::vector<vi> pos, neg;
  int numVar, numInequalities, numElimVar;
  void updatePositions(const Octagon &);
  void operate(std::ostream &, int, Octagon, Octagon);
 public:
  OctagonsInterpolant(std::istream &);
  ~OctagonsInterpolant();
  void printMessage(std::ostream &, bool, Octagon &, Octagon &, Octagon &);
  void interpolation(std::ostream &);
};

#endif
