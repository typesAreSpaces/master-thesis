#ifndef _BOUND_
#define _BOUND_

#include <iostream>

typedef int BoundValue;

struct Bound {
  bool is_infinite;
  bool is_positive;
  BoundValue bound_value;

  Bound();
  Bound(bool);
  Bound(BoundValue);

  void update(BoundValue);
  void normalize(BoundValue);

  friend Bound operator + (Bound const &, Bound const &);
  friend Bound operator - (Bound const &, Bound const &);
  friend bool  operator ==(Bound const &, Bound const &);
  friend bool  operator !=(Bound const &, Bound const &);
  friend bool  operator < (Bound const &, Bound const &);
  friend bool  operator > (Bound const &, Bound const &);
  friend bool  operator <=(Bound const &, Bound const &);
  friend bool  operator >=(Bound const &, Bound const &);
  friend std::ostream & operator << (std::ostream &, Bound const &);
};

#endif
