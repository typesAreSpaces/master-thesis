#include "Bounds.h"

Bounds::Bounds() : std::vector<Bound>(), default_value()
{
}

void Bounds::insert(UtvpiPosition index, Bound const & value){
  if(size() <= index)
    this->resize(index + 1, default_value);
  this->operator[](index) = std::min(this->operator[](index), value);
}

void Bounds::remove(UtvpiPosition position){
  if(size() <= position)
    throw "Out of bounds error @ Bounds::remove.";
  this->operator[](position) = Bound();
}

std::ostream & operator << (std::ostream & os, Bounds const & bounds){
  UtvpiPosition index = 0;
  for(auto const & entry : bounds){
    if(!entry.is_infinite){
      os << Octagon(index) << " <= " << entry 
        << " (Position) " << index << std::endl;
    }
    index++;
  }
  return os;
}
