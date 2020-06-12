#include "VarPositions.h"

VarPositions::VarPositions() :
  index_var_positions()
{
}

std::ostream & operator << (std::ostream & os, VarPositions const & varpos){
  unsigned index = 0;
  os << "Note: x_0 = 0" << std::endl;
  for(auto const & entry : varpos.index_var_positions){
    os << "x_" << index++ << ":" << std::endl;
    os << "Positive positions" << std::endl;
    for(auto const & pos : entry.first)
      os << pos << " ";
    os << std::endl;
    os << "Negative positions" << std::endl;
    for(auto const & pos : entry.second)
      os << pos << " ";
    os << std::endl;
  }
  return os;
}
