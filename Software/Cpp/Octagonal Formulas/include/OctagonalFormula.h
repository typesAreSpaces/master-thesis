#ifndef _OCTFORMULAS_
#define _OCTFORMULAS_

#include <cmath>
#include <vector>
#include <iostream>
#include <fstream>
// There is a relation between MAX_NUM_VARS (= m) and MAX_NUM_INEQS
// In fact, the maximal octagonal formula is + m + (m - 1)
// Hence, the maximum number of inequalities is 2*m^2 + 4*m + 1
#define MAX_NUM_VARS  500
#define MAX_NUM_INEQS 2*MAX_NUM_VARS*MAX_NUM_VARS + 4*MAX_NUM_VARS + 10
#define INF           10000000

typedef std::vector<int> inequalities;
typedef std::vector< std::vector<int> > positions;
typedef std::vector<int> vi;

extern bool debug;

class OctagonalFormula{
 private:
  char s1, s2;
  int n1, n2;
public:
  OctagonalFormula(char, int, char, int);
  // 'invPosition' :: int -> OctagonalFormula
  // OctagonalFormula invPosition(int);
  OctagonalFormula(int);
  ~OctagonalFormula();
  int getS1();
  int getS2();
  char getN1();
  char getN2();
  static int numgroup(int);
  // position :: Octagonal -> int
  int position();
  void normal(int &);
  std::ostream & print (std::ostream &);
};

void updatePositions(OctagonalFormula, positions &, positions &);

void printMessage(std::ostream &, bool, OctagonalFormula &, OctagonalFormula &, OctagonalFormula &, inequalities &);

void operate(std::ostream &, int, OctagonalFormula, OctagonalFormula, inequalities &, positions &, positions &);

#endif
