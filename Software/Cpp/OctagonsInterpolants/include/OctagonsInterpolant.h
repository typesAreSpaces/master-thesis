#ifndef _OCTAGONSINTER_
#define _OCTAGONSINTER_
#define DEBUG_OCT_INTER_ false
#define PRINT_MSG        false
#define PRINT_INTER      false

#include <vector>
#include <set>
#include <map>
#include <z3++.h>
#include "Octagon.h"

typedef std::map<unsigned, int> TablePosition;

class OctagonsInterpolant{
 private:
  z3::context & ctx;
  std::vector<int> bounds, variables_to_eliminate;
  std::vector<std::vector<int> > positive_var_positions, negative_var_positions;
  int num_vars, num_inequalities, num_uncomm_vars;
  std::vector<std::string> names;
  void updatePositions(Octagon &);
  void operateBoth2Args(int, Octagon &, Octagon &);
  void operateBoth1Arg(int, Octagon &, Octagon &);
  void operate2Args1Arg(int, Octagon &, Octagon &);
  void getSymbols(const z3::expr &, int &, TablePosition &, std::vector<std::string> &);
  void auxiliarGetSymbols(const z3::expr &, int &, TablePosition &, std::vector<std::string> &);
 public:
  OctagonsInterpolant(z3::context & ctx, std::istream &);
  OctagonsInterpolant(const z3::expr &, const std::vector<std::string> &);
  ~OctagonsInterpolant();
  void printMessage(Octagon &, Octagon &, Octagon &);
  z3::expr buildInterpolant();
};

#endif
