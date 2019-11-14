#include "OctagonalFormula.h"

bool debug = true;

OctagonalFormula::OctagonalFormula(char s1, int n1, char s2, int n2) :
  s1(s1), n1(n1), s2(s2), n2(n2) {
}

OctagonalFormula::OctagonalFormula (int n){
  int p = OctagonalFormula::numgroup(n);
  if(n < 2*p*p + 2*p + 1){
    int p2 = 2*p*p;
    if(n == p2)
      s1 = '-', n1 = p, s2 = '+', n2 = -1;
    else{
      if((n - p2) % 2 == 0)
	s1 = '-', n1 = p, s2 = '+', n2 = ceil((n - p2)/2.0) - 1;
      else
	s1 = '-', n1 = p, s2 = '-', n2 = ceil((n - p2)/2.0) - 1;
    }
  }
  else{
    int p2 = 2*p*p + 2*p + 1;
    if(n == p2)
      s1 = '+', n1 = p, s2 = '+', n2 = -1;
    else{
      if((n - p2) % 2 == 0)
	s1 = '+', n1 = p, s2 = '+', n2 = ceil((n - p2)/2.0) - 1;
      else
	s1 = '+', n1 = p, s2 = '-', n2 = ceil((n - p2)/2.0) - 1;
    }
  }
}

OctagonalFormula::~OctagonalFormula(){}

char OctagonalFormula::getS1(){
  return s1;
}

char OctagonalFormula::getS2(){
  return s2;
}

int OctagonalFormula::getN1(){
  return n1;
}

int OctagonalFormula::getN2(){
  return n2;
}

int OctagonalFormula::numgroup(int n){
  return floor(sqrt(n/2));
}

int OctagonalFormula::position(){
  if(s1 == '-' && n2 == -1)
    return 2*n1*n1;
  if(s1 == '+' && n2 == -1)
    return 2*n1*n1 + 2*n1 + 1;
  if(s1 == '-'){
    if(s2 == '-')
      return 2*n1*n1 + 2*(n2 + 1) - 1; 
    else
      return 2*n1*n1 + 2*(n2 + 1);
  }
  else{
    if(s2 == '-')
      return 2*n1*n1 + 2*n1 + 1 + 2*(n2 + 1) - 1; 
    else
      return 2*n1*n1 + 2*n1 + 1 + 2*(n2 + 1);
  }
}

void OctagonalFormula::normalize(int & b){
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
    b /= 2;
  }
  // If s1 x1 s2 x2 <= a with x2 > x1, then return s2 x2 s1 x1 <= a
  else if(n2 > n1){
    int _s1 = getS1(), _s2 = getS2(), _n1 = getN1(), _n2 = getN2();
    s1 = _s2;
    n1 = _n2;
    s2 = _s1;
    n2 = _n1;
  }
}

std::ostream & OctagonalFormula::print(std::ostream & os){
  if(n2 == -1){
    // OctagonalFormulas of the form +/- 0 +/- -1
    // is reserved for constant cases
    if(n1 == 0 || n1 == -1)
      os << "Octagonal Formula: 0";
    // OctagonalFormulas of the form +/- x +/- -1
    // is reserved for single variable inequalities
    else
      os << "Octagonal Formula: " << s1 << " x_" << n1;
  }
  else
    os << "Octagonal Formula: " << s1 << " x_" << n1 << " " << s2 << " x_" << n2;
  return os;
}

std::ostream & operator << (std::ostream & os, OctagonalFormula & x){
  return x.print(os);
}
