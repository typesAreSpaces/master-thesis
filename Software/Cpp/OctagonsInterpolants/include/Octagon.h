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
  char first_sign, second_sign;
  int first_var_position, second_var_position;
  int utvpi_position;
  
public:
  Octagon(char, char, int, int);
  Octagon(int);
  ~Octagon();

  const char getFirstSign() const;
  const char getSecondSign() const;
  const int  getFirstVarPosition() const;
  const int  getSecondVarPosition() const;
  const int  getUtvpiPosition();
  
  void setUtvpiPosition(char, char, int, int);
  int  normalize(int);

  friend std::ostream & operator << (std::ostream &, const Octagon &);
};

#endif
