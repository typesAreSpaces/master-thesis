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
  char getS1();
  char getS2();
  int getN1();
  int getN2();
  static int numgroup(int);
  // position :: Octagonal -> int
  int position();
  void normalize(int &);
  std::ostream & print (std::ostream &);
  friend std::ostream & operator << (std::ostream &, OctagonalFormula &);
};

#endif
