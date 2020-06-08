#ifndef _OCTAGON_
#define _OCTAGON_

#include <iostream>
#include <assert.h>
#include <cmath>

enum Coeff { NEG, ZERO, POS };
typedef unsigned Variable; // This type doesn't include 0
typedef unsigned UtviPosition;

struct Octagon {
  Coeff    coeff1, coeff2;
  Variable var1, var2;

  Octagon(Coeff, Variable, Coeff, Variable);
  Octagon(UtviPosition);

  UtviPosition getUtviPosition() const;
  
  friend std::ostream & operator << (std::ostream &, Octagon const &);
};

#endif
