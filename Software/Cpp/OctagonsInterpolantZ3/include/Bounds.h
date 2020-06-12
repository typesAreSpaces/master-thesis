#ifndef _BOUNDS_
#define _BOUNDS_

#include <vector>
#include "Bound.h"
#include "Octagon.h"

class Bounds : public std::vector<Bound> {
  Bound default_value;

  public:
  Bounds();

  void insert(UtvpiPosition, Bound const &);
  void remove(UtvpiPosition);
  friend std::ostream & operator << (std::ostream &, Bounds const &);
};

#endif
