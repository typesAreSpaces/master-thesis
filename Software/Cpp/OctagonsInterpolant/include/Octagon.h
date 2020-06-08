#ifndef _OCTAGON_
#define _OCTAGON_

#include <cmath>
#include <iostream>

typedef unsigned UtviPosition;

class Octagon {
  
private:
  char first_sign, second_sign;
  int  first_var_position, second_var_position;
  int  utvpi_position;
  
public:
  Octagon(char, char, int, int);
  Octagon(int);
  ~Octagon();

  char const  getFirstSign()         const;
  char const  getSecondSign()        const;
  int  const  getFirstVarPosition()  const;
  int  const  getSecondVarPosition() const;
  int  const  getUtvpiPosition();
  int  const  num_args()             const;
  
  void setUtvpiPosition(char, char, int, int);
  int  normalize(int);

  friend std::ostream & operator << (std::ostream &, const Octagon &);
};

#endif
