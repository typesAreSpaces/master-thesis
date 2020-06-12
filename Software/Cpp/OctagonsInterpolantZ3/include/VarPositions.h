#ifndef _VAR_POSITIONS_
#define _VAR_POSITIONS_

#include <iostream>
#include <vector>
#include <set>
#include "Octagon.h"

typedef std::set<VarValue> Positions;

class VarPositions : public std::vector<std::pair<Positions, Positions> > {

  public:
  VarPositions();

  inline void insertPositivePosition(VarValue index, UtvpiPosition value){
    (*this)[index].first.insert(value);
  }
  inline void insertNegativePosition(VarValue index, UtvpiPosition value){
    (*this)[index].second.insert(value);
  }

  friend std::ostream & operator << (std::ostream &, VarPositions const &);
};

#endif
