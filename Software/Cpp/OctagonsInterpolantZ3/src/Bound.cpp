#include "Bound.h"

Bound::Bound() : 
  is_infinite(true),
  is_positive(true),
  bound_value(0)
{
}

Bound::Bound(bool is_positive) : 
  is_infinite(true), 
  is_positive(is_positive), 
  bound_value(0)
{
}

Bound::Bound(BoundValue bound_value) :
  is_infinite(false), 
  is_positive(bound_value < 0 ? false : true),
  bound_value(bound_value)
{
}

void Bound::update(BoundValue new_bound_value){
  bound_value = new_bound_value;
}

void Bound::normalize(BoundValue scale_factor){
  if(is_infinite)
    return;
  if(bound_value >= 0){
    bound_value /= scale_factor; 
    return;
  }
  bound_value = (bound_value-1)/scale_factor;
}

Bound operator + (Bound const & b1, Bound const & b2){
  if(!b1.is_infinite && !b2.is_infinite)
    return Bound(b1.bound_value + b2.bound_value);
  if(!b1.is_infinite && b2.is_infinite)
    return Bound(b2.is_positive);
  if(b1.is_infinite && !b2.is_infinite)
    return Bound(b1.is_positive);
  //if(b1.is_infinite && b2.is_infinite)
  if(!b1.is_positive && !b2.is_positive)
    return Bound(false);
  return Bound(true);
}

Bound operator - (Bound const & b1, Bound const & b2){
  if(!b1.is_infinite && !b2.is_infinite)
    return Bound(b1.bound_value - b2.bound_value);
  if(!b1.is_infinite && b2.is_infinite)
    return Bound(!b2.is_positive);
  if(b1.is_infinite && !b2.is_infinite)
    return Bound(!b1.is_positive);
  //if(b1.is_infinite && b2.is_infinite)
  if(!b1.is_positive && b2.is_positive)
    return Bound(false);
  return Bound(true);
}

bool operator ==(Bound const & b1, Bound const & b2){
  return b1.bound_value == b2.bound_value 
    && b1.is_infinite == b2.is_infinite 
    && b1.is_positive == b2.is_positive;
}

bool operator !=(Bound const & b1, Bound const & b2){
  return b1.bound_value != b2.bound_value 
    || b1.is_infinite != b2.is_infinite 
    || b1.is_positive != b2.is_positive;
}

bool operator < (Bound const & b1, Bound const & b2){
  if(!b1.is_infinite && !b2.is_infinite)
    return b1.bound_value < b2.bound_value;
  if(!b1.is_infinite && b2.is_infinite)
    return b2.is_positive;
  if(b1.is_infinite && !b2.is_infinite)
    return !b1.is_positive;
  //if(b1.is_infinite && b2.is_infinite)
  if(!b1.is_positive && b2.is_positive)
    return true;
  return false;
}

bool operator <=(Bound const & b1, Bound const & b2){
  if(!b1.is_infinite && !b2.is_infinite)
    return b1.bound_value <= b2.bound_value;
  if(!b1.is_infinite && b2.is_infinite)
    return b2.is_positive;
  if(b1.is_infinite && !b2.is_infinite)
    return !b1.is_positive;
  //if(b1.is_infinite && b2.is_infinite)
  if(b1.is_positive && !b2.is_positive)
    return false;
  return true;
}

bool operator > (Bound const & b1, Bound const & b2){
  if(!b1.is_infinite && !b2.is_infinite)
    return b1.bound_value > b2.bound_value;
  if(!b1.is_infinite && b2.is_infinite)
    return !b2.is_positive;
  if(b1.is_infinite && !b2.is_infinite)
    return b1.is_positive;
  //if(b1.is_infinite && b2.is_infinite)
  if(b1.is_positive && !b2.is_positive)
    return true;
  return false;
}

bool operator >=(Bound const & b1, Bound const & b2){
  if(!b1.is_infinite && !b2.is_infinite)
    return b1.bound_value >= b2.bound_value;
  if(!b1.is_infinite && b2.is_infinite)
    return !b2.is_positive;
  if(b1.is_infinite && !b2.is_infinite)
    return b1.is_positive;
  //if(b1.is_infinite && b2.is_infinite)
  if(!b1.is_positive && b2.is_positive)
    return false;
  return true;
}

std::ostream & operator << (std::ostream & os, Bound const & bound){
  if(bound.is_infinite)
    return os << (bound.is_positive ? "+" : "-") << "inf";
  return os << bound.bound_value;
}
