#include "Bounds.h"

Bounds::Bounds() : std::vector<Bound>(), default_value()
{
}

void Bounds::insert(unsigned index, Bound const & value){
  if(size() <= index)
    this->resize(index + 1, default_value);
  this->operator[](index) = std::min(this->operator[](index), value);
}

std::ostream & operator << (std::ostream & os, Bounds const & bounds){
  UtvpiPosition index = 0;
  for(auto const & entry : bounds){
    if(!entry.is_infinite){
      Octagon tmp(index);
      os << tmp << " <= " << entry 
        << " (Position) " << index << std::endl;
    }
    index++;
  }
  return os;
}
