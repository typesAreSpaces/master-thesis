#ifndef _OCTAGONSINTER_
#define _OCTAGONSINTER_
#define DEBUG_OCT_INTER_ false
#define PRINT_MSG        false
#define PRINT_INTER      false

#include <vector>
#include <set>
#include <z3++.h>
#include "Octagon.h"

class OctagonsInterpolant{
 private:
  std::vector<int> bounds, variables_to_eliminate;
  std::vector<std::vector<int> > positive_var_positions, negative_var_positions;
  int num_vars, num_inequalities, num_uncomm_vars;
  void updatePositions(Octagon &);
  void operateBoth2Args(int, Octagon &, Octagon &);
  void operateBoth1Arg(int, Octagon &, Octagon &);
  void operate2Args1Arg(int, Octagon &, Octagon &);
 public:
  OctagonsInterpolant(std::istream &);
  OctagonsInterpolant(const z3::expr &, const std::set<std::string> &);
  ~OctagonsInterpolant();
  void printMessage(Octagon &, Octagon &, Octagon &);
  void buildInterpolant();
};

#endif
