#ifndef _OCTAGON_
#define _OCTAGON_
#define DEBUG_VAR 0

#define Octagon_return \
  assert((coeff2 == ZERO && var2 == 0) || (coeff2 != ZERO && var2 > 0)); \
  assert((coeff1 == ZERO && var1 == 0) || (coeff1 != ZERO && var1 > 0));\
  assert(var1 > var2 || (coeff1 == coeff2 && coeff1 == ZERO));\
  return

#include <iostream>
#include <limits>
#include <assert.h>
#include <cmath>

enum Coeff { NEG, ZERO, POS };
typedef unsigned UtvpiPosition;
typedef unsigned VarValue; 

struct Var {
  static UtvpiPosition max_utvpi_value;
  // Depending on the type of VarValue and UtviPosition
  // value can encode more variables. 
  VarValue value;

  Var(VarValue);

  inline friend bool operator < (Var const &, Var const &);
  inline friend bool operator > (Var const &, Var const &);
  inline friend bool operator ==(Var const &, Var const &);
  inline friend bool operator !=(Var const &, Var const &);
  inline friend bool operator ==(Var const &, VarValue);
  inline friend bool operator !=(Var const &, VarValue);
};

struct Octagon {
  Coeff coeff1, coeff2;
  Var   var1, var2;

  Octagon(Coeff, VarValue, Coeff, VarValue);
  Octagon(UtvpiPosition);

  UtvpiPosition getUtviPosition() const;
  
  friend std::ostream & operator << (std::ostream &, Octagon const &);
};

#endif
