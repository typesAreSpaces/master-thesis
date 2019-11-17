#ifndef _OCTAGON_
#define _OCTAGON_

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

class Octagon{
 private:
  char s1, s2;
  int n1, n2;
  int position;
public:
  Octagon(char, char, int, int);
  // 'invPosition' :: int -> Octagon
  // Octagon invPosition(int);
  Octagon(int);
  ~Octagon();

  const char getS1() const;
  const char getS2() const;
  const int getN1() const;
  const int getN2() const;
  
  const int getPosition() const;
  int normalize(int);

  friend std::ostream & operator << (std::ostream &, const Octagon &);
};

#endif
