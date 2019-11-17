#include "structures.hpp"

bool debug = true;

OctagonalFormula::OctagonalFormula(char s1, int n1, char s2, int n2):
  s1(s1), n1(n1), s2(s2), n2(n2)
{};

void OctagonalFormula::print(std::ostream & fileOut){
  if(n2 == -1){
    // OctagonalFormulas of the form +/- 0 +/- -1
    // is reserved for constant cases
    if(n1 == 0 || n1 == -1)
      fileOut << "Octagonal Formula: 0";
    // OctagonalFormulas of the form +/- x +/- -1
    // is reserved for single variable inequalities
    else
      fileOut << "Octagonal Formula: " << s1 << " x_" << n1;
  }
  else{
    fileOut << "Octagonal Formula: " << s1 << " x_" << n1 << " " << s2 << " x_" << n2;
  }
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

OctagonalFormula normal(OctagonalFormula x, int & b){
  // If +/- x + -/+ x <= a, then return 0 <= a
  if(x.s1 != x.s2 && x.n1 == x.n2){
    OctagonalFormula temp = x;
    // This is the encoding for 0 <= a
    temp.n1 = 0;
    temp.n2 = -1;
    return temp;
  }
  // If +/- x +/- x <= a, then return +/- x + 0 <= floor(a/2)
  else if(x.s1 == x.s2 && x.n1 == x.n2){
    OctagonalFormula temp = x;
    temp.n2 = -1;
    b /= 2;
    return temp;
  }
  // If s1 x1 s2 x2 <= a with x2 > x1, then return s2 x2 s1 x1 <= a
  else if(x.n2 > x.n1){
    OctagonalFormula temp = x;
    temp.s1 = x.s2;
    temp.n1 = x.n2;
    temp.s2 = x.s1;
    temp.n2 = x.n1;
    return temp;
  }
  else
    return x;
}

int numgroup(int n){
  return floor(sqrt(n/2));
}

OctagonalFormula invPosition(int n){
  int p = numgroup(n);
  if(n < 2*p*p + 2*p + 1){
    int p2 = 2*p*p;
    if(n == p2)
      return OctagonalFormula('-', p, '+', -1);
    else{
      if((n - p2) % 2 == 0)
	return OctagonalFormula('-', p, '+', ceil((n - p2)/2.0) - 1);
      else
	return OctagonalFormula('-', p, '-', ceil((n - p2)/2.0) - 1);
    }
  }
  else{
    int p2 = 2*p*p + 2*p + 1;
    if(n == p2)
      return OctagonalFormula('+', p, '+', -1);
    else{
      if((n - p2) % 2 == 0)
	return OctagonalFormula('+', p, '+', ceil((n - p2)/2.0) - 1);
      else
	return OctagonalFormula('+', p, '-', ceil((n - p2)/2.0) - 1);
    }
  }
}

void updatePositions(OctagonalFormula f, positions & pos, positions & neg){
  char s1 = f.s1, s2 = f.s2;
  int n1 = f.n1, n2 = f.n2;
  if(s1 == '+'){
    pos[n1].push_back(f.position());
  }
  else if (s1 == '-'){
    neg[n1].push_back(f.position());
  }
  if(s2 == '+'){
    pos[n2].push_back(f.position());
  }
  else if (s2 == '-'){
    neg[n2].push_back(f.position());
  }
}

void printMessage(std::ostream & fileOut, bool debug, OctagonalFormula & x, OctagonalFormula & y, OctagonalFormula & z, inequalities & A){
  if(debug){
    fileOut << "Taking inequalities:" << std::endl;
    x.print(fileOut);
    fileOut << " <= " << A[x.position()] << std::endl;
    y.print(fileOut);
    fileOut << " <= " << A[y.position()] << std::endl;
    fileOut << "To produce this" << std::endl;
    z.print(fileOut);
    fileOut << " <= " << A[z.position()] << std::endl << std::endl;
  }
}

void operate(std::ostream & fileOut, int elim, OctagonalFormula x, OctagonalFormula y, inequalities & A, positions & pos, positions & neg){
  char s11 = x.s1, s12 = x.s2, s21 = y.s1, s22 = y.s2, s1, s2;
  int n11 = x.n1, n12 = x.n2, n21 = y.n1, n22 = y.n2, n1, n2;
  int b1 = A[x.position()], b2 = A[y.position()];
  // Case +/- x (...); -/+ x (...) 
  if(n11 == n21 && n11 == elim){
    // Case +/- x +/- y <= b1; -/+ x +/- y <= b2 
    if(s12 == s22 && n12 == n22){
      OctagonalFormula temp(s12, n12, '+', -1);
      A[temp.position()] = std::min(A[temp.position()], (b1 + b2)/2);
      updatePositions(temp, pos, neg);
      printMessage(fileOut, debug, x, y, temp, A);
    }
    // Case +/- x +/- y <= b1; -/+ x -/+ y <= b2
    else if(s12 != s22 && n12 == n22){
      // Do nothing!
      if(debug)
	fileOut << "Couldn't produce anything interesting (0 <= a)" << std::endl << std::endl;
    }
    // Case +/- x s1 y1 <= b1; -/+ x s2 y2 <= b2; (with y1 != y2) 
    else{
      // Reorder as necessary so
      // s1 y1 s2 y2 <= b (with y1 > y2)
      if(n12 > n22){
	s1 = s12;
	n1 = n12;
	s2 = s22;
	n2 = n22;
      }
      else{
	s2 = s12;
	n2 = n12;
	s1 = s22;
	n1 = n22;
      }
      OctagonalFormula temp(s1, n1, s2, n2);
      A[temp.position()] = std::min(A[temp.position()], b1 + b2);
      updatePositions(temp, pos, neg);
      printMessage(fileOut, debug, x, y, temp, A);
    }
  }
  // Case +/- x (...); (..) -/+ x (..)
  else if(n11 == n22 && n11 == elim){
    // Case +/- x +/- y <= b1; +/- y -/+ x <= b2
    if(s12 == s21 && n12 == n21){
      OctagonalFormula temp(s12, n12, '+', -1);	
      A[temp.position()] = std::min(A[temp.position()], (b1 + b2)/2);
      updatePositions(temp, pos, neg);
      printMessage(fileOut, debug, x, y, temp, A);
    }
    // Case +/- x +/- y <= b1; -/+ y -/+ x <= b2
    else if(s12 != s21 && n12 == n21){
      // Do nothing!
      if(debug)
	fileOut << "Couldn't produce anything interesting (0 <= a)" << std::endl << std::endl;
    }
    // Case +/- x s1 y1 <= b1; s2 y2 -/+ x <= b2; (with y1 != y2) 
    else{
      // Reorder as necessary so
      // s1 y1 s2 y2 <= b (with y1 > y2)
      if(n12 > n21){
	s1 = s12;
	n1 = n12;
	s2 = s21;
	n2 = n21;
      }
      else{
	s2 = s12;
	n2 = n12;
	s1 = s21;
	n1 = n21;
      }
      OctagonalFormula temp(s1, n1, s2, n2);
      A[temp.position()] = std::min(A[temp.position()], b1 + b2);
      updatePositions(temp, pos, neg);
      printMessage(fileOut, debug, x, y, temp, A);
    }
  }
  // Case (..) +/- x (..); -/+ x (...)
  else if(n12 == n21 && n12 == elim){
    // Case +/- y +/- x <= b1; -/+ x +/- y <= b2
    if(s11 == s22 && n11 == n22){
      OctagonalFormula temp(s11, n11, '+', -1);
      A[temp.position()] = std::min(A[temp.position()], (b1 + b2)/2);
      updatePositions(temp, pos, neg);
      printMessage(fileOut, debug, x, y, temp, A);
    }
    // Case +/- y +/- x <= b1; -/+ x -/+ y <= b2
    else if(s11 != s22 && n11 == n22){
      // Do nothing!
      if(debug)
	fileOut << "Couldn't produce anything interesting (0 <= a)" << std::endl << std::endl;
    }
    // Case s1 y1 +/- x <= b1; -/+ x s2 y2 <= b2; (with y1 != y2)
    else{
      // Reorder as necessary so
      // s1 y1 s2 y2 <= b (with y1 > y2)
      if(n11 > n22){
	s1 = s11;
	n1 = n11;
	s2 = s22;
	n2 = n22;
      }
      else{
	s2 = s11;
	n2 = n11;
	s1 = s22;
	n1 = n22;
      }
      OctagonalFormula temp(s1, n1, s2, n2);
      A[temp.position()] = std::min(A[temp.position()], b1 + b2);
      updatePositions(temp, pos, neg);
      printMessage(fileOut, debug, x, y, temp, A);
    }
  }
  // Case (..) +/- x (..); (..) -/+ x (..)
  else if(n12 == n22 && n12 == elim){
    // Case +/- y +/- x <= b1; +/- y -/+ x <= b2
    if(s11 == s21 && n11 == n21){
      OctagonalFormula temp(s11, n11, '+', -1);
      A[temp.position()] = std::min(A[temp.position()], (b1 + b2)/2);
      updatePositions(temp, pos, neg);
      printMessage(fileOut, debug, x, y, temp, A);
    }
    // Case +/- y +/- x <= b1; -/+ y -/+ x <= b2
    else if(s11 != s21 && n11 == n21){
      // Do nothing!
      if(debug)
	fileOut << "Couldn't produce anything interesting (0 <= a)" << std::endl << std::endl;
    }
    // Case s1 y1 +/- x <= b1; s2 y2 -/+ x <= b2; (with y1 != y2)
    else{
      // Reorder as necessary so
      // s1 y1 s2 y2 <= b (with y1 > y2)
      if(n11 > n21){
	s1 = s11;
	n1 = n11;
	s2 = s21;
	n2 = n21;
      }
      else{
	s2 = s11;
	n2 = n11;
	s1 = s21;
	n1 = n21;
      }
      OctagonalFormula temp(s1, n1, s2, n2);
      A[temp.position()] = std::min(A[temp.position()], b1 + b2);
      updatePositions(temp, pos, neg);
      printMessage(fileOut, debug, x, y, temp, A);
    }
  }
  //A[position(x)] = INF;
  //A[position(y)] = INF;
}
