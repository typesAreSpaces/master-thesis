#ifndef _VAR_POSITIONS_
#define _VAR_POSITIONS_

#include <iostream>
#include <vector>
#include <set>
#include "Octagon.h"

typedef std::set<VarValue> Positions;

class VarPositions {
  std::vector<std::pair<Positions, Positions> > index_var_positions;

  public:
  VarPositions();

  inline void insertPositivePosition(VarValue index, UtvpiPosition value){
    index_var_positions[index].first.insert(value);
  }
  inline void insertNegativePosition(VarValue index, UtvpiPosition value){
    index_var_positions[index].second.insert(value);
  }
  inline void resize(unsigned new_size){
    index_var_positions.resize(new_size);
  }
  inline unsigned size() const {
    return index_var_positions.size();
  }
  friend std::ostream & operator << (std::ostream &, VarPositions const &);
};

#endif
