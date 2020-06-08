#ifndef _OCTAGONSINTER_
#define _OCTAGONSINTER_

#define DEBUG_OCT_INTER_ 0
#define PRINT_MSG        0
#define PRINT_INTER      0

// There is a relation between MAX_NUM_VARS (= m) and MAX_NUM_INEQS
// In fact, the maximal octagonal formula is + m + (m - 1)
// Hence, the maximum number of inequalities is 2*m^2 + 4*m + 1
#define MAX_NUM_VARS  500
#define MAX_NUM_INEQS 2*(MAX_NUM_VARS+1)*(MAX_NUM_VARS+1) + 1
#define INF           2147483647

#include <vector>
#include <set>
#include <map>
#include <z3++.h>
#include "Octagon.h"

typedef std::map<unsigned, int> TablePosition;

class OctagonsInterpolant {
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
  OctagonsInterpolant(z3::expr const &, std::vector<std::string> const &);
  ~OctagonsInterpolant();
  void printMessage(Octagon &, Octagon &, Octagon &);
  z3::expr buildInterpolant();
};

#endif
