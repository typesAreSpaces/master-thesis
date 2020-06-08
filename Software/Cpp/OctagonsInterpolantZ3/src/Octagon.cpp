#include "Octagon.h"

Octagon::Octagon(Coeff coeff1, Variable var1, Coeff coeff2, Variable var2) :
  coeff1(coeff1), coeff2(coeff2),
  var1(var1), var2(var2)
{
  assert((coeff2 == ZERO && var2 == 0) || (coeff2 != ZERO && var2 > 0));
  assert((coeff1 == ZERO && var1 == 0) || (coeff1 != ZERO && var1 > 0));
  assert(var1 > var2 || (coeff1 == coeff2 && coeff1 == ZERO));
}

Octagon::Octagon(UtviPosition pos){
  if(pos == 0){
    coeff1 = ZERO;
    coeff2 = ZERO;
    var1 = 0;
    var2 = 0;
    return;
  }
  var1 = (unsigned)(sqrt(pos/2) + 0.5); // KEEP: working here
  unsigned initial_position_group = 2*(var1-1)*(var1-1) + 1;
  unsigned half_size_group = 2*var1 - 1;

  std::cout << var1 << std::endl;

  if(pos < initial_position_group + half_size_group){
    coeff1 = NEG;
    if(pos == initial_position_group){
      coeff2 = ZERO;
      var2 = 0;
      return;
    }
    std::cout << "Var-1 " << var1 << std::endl;
    std::cout << "Pos " << pos << std::endl;
    std::cout << "Initial " << initial_position_group << std::endl;
    assert(pos > initial_position_group);
    // Then temp is of the form 1 + 2j (+ 1)
    unsigned temp = pos - initial_position_group - 1;
    var2 = temp/2;
    if(temp % 2 == 0){
      coeff2 = POS;
      return;
    }
    coeff2 = NEG;
    return;
  }

  coeff1 = POS;
  if(pos == initial_position_group + half_size_group){
    coeff2 = ZERO;
    var2 = 0;
    return;
  }
  // Then temp is of the form 1 + 2j (+ 1)
  unsigned temp = pos - initial_position_group - 1;
  var2 = temp/2;
  if(temp % 2 == 0){
    coeff2 = POS;
    return;
  }
  coeff2 = NEG;
  return;
}

UtviPosition Octagon::getUtviPosition() const {

  unsigned initial_position_group = 2*(var1-1)*(var1-1) + 1;
  unsigned sign_a_offset, sign_b_offset;

  switch(coeff1){
    case NEG:
      sign_a_offset = 0;
      break;
    case ZERO:
      return 0;
    case POS:
      sign_a_offset = 2*(var1 - 1) + 1;
      break;
  }
  switch(coeff2){
    case NEG:
      sign_b_offset = 1 + 2*(var2 - 1);
      break;
    case ZERO:
      sign_b_offset = 0;
      break;
    case POS:
      sign_b_offset = 1 + 2*(var2 - 1) + 1;
      break;
  }
  return initial_position_group + sign_a_offset + sign_b_offset;
}

std::ostream & operator << (std::ostream & os, Octagon const & oct){
  os << "Octagon: ";
  switch(oct.coeff1){
    case NEG:
      os << "- x_" << oct.var1;
      switch(oct.coeff2){
        case NEG:
          os << " - x_" << oct.var2;
          break;
        case ZERO:
          break;
        case POS:
          os << " + x_" << oct.var2;
          break;
      }
      break;
    case ZERO:
      os << "0";
      break;
    case POS: 
      os << "x_" << oct.var1;
      switch(oct.coeff2){
        case NEG:
          os << " - x_" << oct.var2;
          break;
        case ZERO:
          break;
        case POS:
          os << " + x_" << oct.var2;
          break;
      }
      break;
  }
  os << " Position: " << oct.getUtviPosition();
  return os;
}
