#include "VarPositions.h"

VarPositions::VarPositions()
{
}

std::ostream & operator << (std::ostream & os, VarPositions const & varpos){
  unsigned index = 0;
  os << "Note: x_0 = 0" << std::endl;
  for(auto const & entry : varpos){
    if(entry.first.size() + entry.second.size() > 0){
      os << "x_" << index << ":" << std::endl;
      if(entry.first.size() > 0){
        os << "+Positive positions" << std::endl;
        for(auto const & pos : entry.first)
          os << pos << " ";
        os << std::endl;
      }
      if(entry.second.size() > 0){
        os << "-Negative positions" << std::endl;
        for(auto const & pos : entry.second)
          os << pos << " ";
        os << std::endl;
      }
    }
    index++;
  }
  return os;
}
