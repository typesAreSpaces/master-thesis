#include "Octagon.h"

Octagon::Octagon(char first_sign, char second_sign, int first_var_position, int second_var_position) :
  first_sign(first_sign), second_sign(second_sign),
  first_var_position(first_var_position), second_var_position(second_var_position) {
  setUtvpiPosition(first_sign, second_sign, first_var_position, second_var_position);
}

Octagon::Octagon(int n){
  // TODO: What does p2 mean?
  int num_group = floor(sqrt(n/2));
  if(n < 2*num_group*num_group + 2*num_group + 1){
    int p2 = 2*num_group*num_group;
    if(n == p2)
      first_sign = '-',
	first_var_position = num_group,
	second_sign = '+',
	second_var_position = -1;
    else{
      if((n - p2) % 2 == 0)
	first_sign = '-',
	  first_var_position = num_group,
	  second_sign = '+',
	  second_var_position = ceil((n - p2)/2.0) - 1;
      else
	first_sign = '-',
	  first_var_position = num_group,
	  second_sign = '-',
	  second_var_position = ceil((n - p2)/2.0) - 1;
    }
  }
  else{
    int p2 = 2*num_group*num_group + 2*num_group + 1;
    if(n == p2)
      first_sign = '+',
	first_var_position = num_group,
	second_sign = '+',
	second_var_position = -1;
    else{
      if((n - p2) % 2 == 0)
	first_sign = '+',
	  first_var_position = num_group,
	  second_sign = '+',
	  second_var_position = ceil((n - p2)/2.0) - 1;
      else
	first_sign = '+',
	  first_var_position = num_group,
	  second_sign = '-',
	  second_var_position = ceil((n - p2)/2.0) - 1;
    }
  }
  setUtvpiPosition(first_sign, second_sign, first_var_position, second_var_position);
}

Octagon::~Octagon(){}

const char Octagon::getFirstSign() const {
  return first_sign;
}

const char Octagon::getSecondSign() const {
  return second_sign;
}

const int Octagon::getFirstVarPosition() const {
  return first_var_position;
}

const int Octagon::getSecondVarPosition() const {
  return second_var_position;
}

const int Octagon::getUtvpiPosition() {
  this->setUtvpiPosition(first_sign, second_sign, first_var_position, second_var_position);
  return utvpi_position;
}

void Octagon::setUtvpiPosition(char first_sign, char second_sign, int first_var_position, int second_var_position) {  
  if(first_sign == '-'){
    if(second_sign == '-')
      this->utvpi_position = 2*first_var_position*first_var_position + 2*(second_var_position + 1) - 1;
    
    else
      this->utvpi_position = 2*first_var_position*first_var_position + 2*(second_var_position + 1);
    
  }
  else{
    if(second_sign == '-')
      this->utvpi_position = 2*first_var_position*first_var_position + 2*first_var_position + 1 + 2*(second_var_position + 1) - 1;
    
    else
      this->utvpi_position = 2*first_var_position*first_var_position + 2*first_var_position + 1 + 2*(second_var_position + 1);
  }
}

int Octagon::normalize(int bound){
  int result = bound;

  if(first_var_position == second_var_position){
    // If +/- x +/- x <= a, then return +/- x + 0 <= floor(a/2)
    if(first_sign == second_sign){
      second_var_position = -1;
      result /= 2;
    }
    // This is the encoding for 0 <= a
    else{
      first_var_position = 0;
      second_var_position = -1;
    }
  }
  else{
    // If first_sign x1 second_sign x2 <= a with x2 > x1, then return second_sign x2 first_sign x1 <= a
    if(second_var_position > first_var_position){
      int _first_sign = first_sign,
	_second_sign = second_sign,
	_first_var_position = first_var_position,
	_second_var_position = second_var_position;
      // Swapping
      first_sign = _second_sign;
      first_var_position = _second_var_position;
      second_sign = _first_sign;
      second_var_position = _first_var_position;
    }
  }
  
  return result;
}

std::ostream & operator << (std::ostream & os, const Octagon & x){
  if(x.second_var_position == -1){
    // Octagons of the form +/- 0 +/- -1
    // is reserved for constant cases
    if(x.first_var_position == 0 || x.first_var_position == -1)
      os << "Octagonal Formula: 0";
    // Octagons of the form +/- x +/- -1
    // is reserved for single variable inequalities
    else
      os << "Octagonal Formula: " << x.first_sign << " x_" << x.first_var_position;
  }
  else{
    os << "Octagonal Formula: " << x.first_sign << " x_" << x.first_var_position
       << " " << x.second_sign << " x_" << x.second_var_position;
  }
  return os;
}
