#ifndef _STRUCTURES_
#define _STRUCTURES_

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

// Data Structure for Octagonal Interpolation

typedef std::vector<int> inequalities;
typedef std::vector< std::vector<int> > positions;
typedef std::vector<int> vi;

extern bool debug;

class OctagonalFormula{
public:
  char s1, s2;
  int  n1, n2;
  OctagonalFormula(char, int, char, int);
  void print(std::ostream &);
  // position :: Octagonal -> int
  int position();
};

// TODO: Move this function
// into OctagonalFormula class
OctagonalFormula normal(OctagonalFormula, int &);

int numgroup(int);

// invPosition :: int -> OctagonalFormula
OctagonalFormula invPosition(int);

void updatePositions(OctagonalFormula, positions &, positions &);

void printMessage(std::ostream &, bool, OctagonalFormula &, OctagonalFormula &, OctagonalFormula &, inequalities &);

void operate(std::ostream &, int, OctagonalFormula, OctagonalFormula, inequalities &, positions &, positions &);

#endif
