#ifndef _OCTAGONSINTER_
#define _OCTAGONSINTER_
#define DEBUG_OCT_INTER_ true
#define PRINT_MSG        true

#include <iostream>
#include <vector>
#include "Octagon.h"

class OctagonsInterpolant{
 private:
  std::vector<int> bounds, variables_to_eliminate;
  std::vector<std::vector<int> > positive_var_positions, negative_var_positions;
  int num_vars, num_inequalities, num_uncomm_vars;
  void updatePositions(Octagon &);
  void operate(int, Octagon &, Octagon &);
 public:
  OctagonsInterpolant(std::istream &);
  ~OctagonsInterpolant();
  void printMessage(Octagon &, Octagon &, Octagon &);
  void buildInterpolat();
};

#endif
