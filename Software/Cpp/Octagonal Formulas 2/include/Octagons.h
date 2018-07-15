#ifndef _OCTAGONS_
#define _OCTAGONS_

#include <iostream>
#include <vector>
#include "OctagonalFormula.h"

typedef std::vector<int> vi;

class Octagons{
 private:
  vi inequalities, variablesToEliminate;
  std::vector<vi> pos, neg;
  int numVar, numInequalities, numElimVar;
  void updatePositions(OctagonalFormula);
  void operate(std::ostream &, int, OctagonalFormula, OctagonalFormula);
 public:
  Octagons(std::istream &);
  ~Octagons();
  void printMessage(std::ostream &, bool, OctagonalFormula &, OctagonalFormula &, OctagonalFormula &);
  void interpolation(std::ostream &);
};

#endif
