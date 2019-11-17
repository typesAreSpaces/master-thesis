#include "Octagon.h"

Octagon::Octagon(char s1, char s2, int n1, int n2) :
  s1(s1), s2(s2), n1(n1), n2(n2) {
  if(s1 == '-' && n2 == -1)
    this->position = 2*n1*n1;
  if(s1 == '+' && n2 == -1)
    this->position = 2*n1*n1 + 2*n1 + 1;
  if(s1 == '-'){
    if(s2 == '-')
      this->position = 2*n1*n1 + 2*(n2 + 1) - 1; 
    else
      this->position = 2*n1*n1 + 2*(n2 + 1);
  }
  else{
    if(s2 == '-')
      this->position = 2*n1*n1 + 2*n1 + 1 + 2*(n2 + 1) - 1; 
    else
      this->position = 2*n1*n1 + 2*n1 + 1 + 2*(n2 + 1);
  }
}

Octagon::Octagon(int n){
  int num_group = floor(sqrt(n/2));
  if(n < 2*num_group*num_group + 2*num_group + 1){
    int p2 = 2*num_group*num_group;
    if(n == p2)
      s1 = '-', n1 = num_group, s2 = '+', n2 = -1;
    else{
      if((n - p2) % 2 == 0)
	s1 = '-', n1 = num_group, s2 = '+', n2 = ceil((n - p2)/2.0) - 1;
      else
	s1 = '-', n1 = num_group, s2 = '-', n2 = ceil((n - p2)/2.0) - 1;
    }
  }
  else{
    int p2 = 2*num_group*num_group + 2*num_group + 1;
    if(n == p2)
      s1 = '+', n1 = num_group, s2 = '+', n2 = -1;
    else{
      if((n - p2) % 2 == 0)
	s1 = '+', n1 = num_group, s2 = '+', n2 = ceil((n - p2)/2.0) - 1;
      else
	s1 = '+', n1 = num_group, s2 = '-', n2 = ceil((n - p2)/2.0) - 1;
    }
  }
}

Octagon::~Octagon(){}

const char Octagon::getS1() const {
  return s1;
}

const char Octagon::getS2() const {
  return s2;
}

const int Octagon::getN1() const {
  return n1;
}

const int Octagon::getN2() const {
  return n2;
}

const int Octagon::getPosition() const {
  return position;
}

int Octagon::normalize(int bound){
  int result = bound;
  // FIX: Problems here
  // If +/- x + -/+ x <= a, then return 0 <= a
  if(s1 != s2 && n1 == n2){
    // This is the encoding for 0 <= a
    n1 = 0;
    n2 = -1;
  }
  // If +/- x +/- x <= a, then return +/- x + 0 <= floor(a/2)
  else if(s1 == s2 && n1 == n2){
    n2 = -1;
    result /= 2;
  }
  // If s1 x1 s2 x2 <= a with x2 > x1, then return s2 x2 s1 x1 <= a
  else if(n2 > n1){
    int _s1 = s1, _s2 = s2, _n1 = n1, _n2 = n2;
    s1 = _s2;
    n1 = _n2;
    s2 = _s1;
    n2 = _n1;
  }
  return result;
}

std::ostream & operator << (std::ostream & os, const Octagon & x){
  if(x.n2 == -1){
    // Octagons of the form +/- 0 +/- -1
    // is reserved for constant cases
    if(x.n1 == 0 || x.n1 == -1)
      os << "Octagonal Formula: 0";
    // Octagons of the form +/- x +/- -1
    // is reserved for single variable inequalities
    else
      os << "Octagonal Formula: " << x.s1 << " x_" << x.n1;
  }
  else
    os << "Octagonal Formula: " << x.s1 << " x_" << x.n1 << " " << x.s2 << " x_" << x.n2;
  return os;
}
