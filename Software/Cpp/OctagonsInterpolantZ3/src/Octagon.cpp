#include "Octagon.h"

UtvpiPosition Var::max_utvpi_value = sqrt(std::numeric_limits<UtvpiPosition>::max());

Var::Var(VarValue value) : 
  value(value) 
{
  assert(value >= 0 && value < max_utvpi_value);
}

bool operator <(Var const & a, Var const & b){
  return a.value < b.value;
}
bool operator >(Var const & a, Var const & b){
  return a.value > b.value;
}
bool operator ==(Var const & a, Var const & b){
  return a.value == b.value;
}
bool operator !=(Var const & a, Var const & b){
  return a.value != b.value;
}
bool operator ==(Var const & a, VarValue v){
  return a.value == v;
}
bool operator !=(Var const & a, VarValue v){
  return a.value != v;
}

Octagon::Octagon(Coeff coeff1, VarValue value1, Coeff coeff2, VarValue value2) :
  coeff1(coeff1), coeff2(coeff2),
  var1(value1), var2(value2)
{
  Octagon_return;
}

Octagon::Octagon(UtvpiPosition pos) :
  coeff1(ZERO), coeff2(ZERO),
  var1(0), var2(0)
{
  if(pos == 0){
    Octagon_return;
  }

  var1 = (VarValue)(sqrt((pos-1)/2)) + 1;
  // Note: initial_group_position *should not* overflow
  // since var1 is a square root of UtviPosition
  UtvpiPosition initial_group_position = 2*(var1.value-1)*(var1.value-1) + 1, 
                half_size_group = 2*(var1.value-1), separation; 

  // -------------------------------------------------
  // First half (i.e. the sign of var1 is negative)
  if(pos <= initial_group_position + half_size_group){
    coeff1 = NEG;
    // First element of first half
    if(pos == initial_group_position){
      coeff2 = ZERO;
      var2   = 0;
      Octagon_return;
    }
    // ---------------------------------------
    // Rest of the other octagons
    separation = pos - initial_group_position;
    var2 = (separation-1)/2 + 1;
    if(separation % 2 == 0){
      coeff2 = POS;
      Octagon_return;
    }
    coeff2 = NEG;
    Octagon_return;
    // ---------------------------------------
  }
  // -------------------------------------------------

  // -------------------------------------------------------------
  // Second half (i.e. the sign of var1 is positive)
  coeff1 = POS;
  // First element of second half
  if(pos == initial_group_position + half_size_group + 1){
    coeff2 = ZERO;
    var2   = 0;
    Octagon_return;
  }
  // -------------------------------------------------------------
  // Rest of the other octagons
  separation = pos - initial_group_position - half_size_group - 1;
  var2 = (separation-1)/2 + 1;
  if(separation % 2 == 0){
    coeff2 = POS;
    Octagon_return;
  }
  coeff2 = NEG;
  Octagon_return;
  // -------------------------------------------------------------
  // -------------------------------------------------------------
}

UtvpiPosition Octagon::getUtviPosition() const {
  // Note: initial_group_position *should not* overflow
  // since var1 is a square root of UtviPosition
  UtvpiPosition initial_group_position = 2*(var1.value-1)*(var1.value-1) + 1; 
  UtvpiPosition sign_a_offset, sign_b_offset;

  switch(coeff1){
    case NEG:
      sign_a_offset = 0;
      break;
    case ZERO:
      return 0;
    case POS:
      sign_a_offset = 2*(var1.value-1) + 1;
      break;
  }
  switch(coeff2){
    case NEG:
      sign_b_offset = 1 + 2*(var2.value-1);
      break;
    case ZERO:
      sign_b_offset = 0;
      break;
    case POS:
      sign_b_offset = 1 + 2*(var2.value-1) + 1;
      break;
  }
  return initial_group_position + sign_a_offset + sign_b_offset;
}

std::ostream & operator << (std::ostream & os, Octagon const & oct){
  os << "Octagon: ";
  switch(oct.coeff1){
    case NEG:
      os << "- x_" << oct.var1.value;
      switch(oct.coeff2){
        case NEG:
          os << " - x_" << oct.var2.value;
          break;
        case ZERO:
          break;
        case POS:
          os << " + x_" << oct.var2.value;
          break;
      }
      break;
    case ZERO:
      os << "0";
      break;
    case POS: 
      os << "x_" << oct.var1.value;
      switch(oct.coeff2){
        case NEG:
          os << " - x_" << oct.var2.value;
          break;
        case ZERO:
          break;
        case POS:
          os << " + x_" << oct.var2.value;
          break;
      }
      break;
  }
  os << " Position: " << oct.getUtviPosition();
  return os;
}
