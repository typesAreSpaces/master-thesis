#include "Octagons.h"

Octagons::Octagons(std::istream & in) : numVar(-1) {
  int n1, n2, bound;
  char s1, s2;

  // Setting INF for all entries in the inequalities vector
  inequalities.resize(MAX_NUM_INEQS);
  pos.resize(MAX_NUM_VARS), neg.resize(MAX_NUM_VARS);
  for(vi::iterator it = inequalities.begin();
      it != inequalities.end();
      ++it){
    *it = INF;
  }
  
  // ----------------------------------------------------------------
  // Getting the number of inequalities  
  in >> numInequalities;
  for(int i = 0; i < numInequalities; ++i){
    in >> s1 >> n1 >> s2 >> n2 >> bound;
    OctagonalFormula temp(s1, n1, s2, n2);
    // -----------------------------------
    // Normalization
    temp.normalize(bound);
    // -----------------------------------
    updatePositions(temp);
    if(n1 > numVar)
      numVar = n1;
    if(n2 > numVar)
      numVar = n2;
    inequalities[temp.position()] = std::min(inequalities[temp.position()], bound);
  }
  // ----------------------------------------------------------------
  
  // ----------------------------------------------------------------
  // Getting the number of variables to eliminate
  in >> numElimVar;
  for(int i = 0; i < numElimVar; ++i){
    in >> n1;
    variablesToEliminate.push_back(n1);
  }
  // ----------------------------------------------------------------
}

Octagons::~Octagons(){}

void Octagons::updatePositions(OctagonalFormula f){
  char s1 = f.getS1(), s2 = f.getS2();
  int n1 = f.getN1(), n2 = f.getN2();
  if(s1 == '+')
    pos[n1].push_back(f.position());
  else if (s1 == '-')
    neg[n1].push_back(f.position());
  if(s2 == '+')
    pos[n2].push_back(f.position());
  else if (s2 == '-')
    neg[n2].push_back(f.position());
}

void Octagons::printMessage(std::ostream & fileOut, bool debug, OctagonalFormula & x, OctagonalFormula & y, OctagonalFormula & z){
  if(debug){
    fileOut << "Taking inequalities:" << std::endl;
    x.print(fileOut);
    fileOut << " <= " << inequalities[x.position()] << std::endl;
    y.print(fileOut);
    fileOut << " <= " << inequalities[y.position()] << std::endl;
    fileOut << "To produce this" << std::endl;
    z.print(fileOut);
    fileOut << " <= " << inequalities[z.position()] << std::endl << std::endl;
  }
}

void Octagons::operate(std::ostream & fileOut, int elim, OctagonalFormula x, OctagonalFormula y){
  char s11 = x.getS1(), s12 = x.getS2(), s21 = y.getS1(), s22 = y.getS2(), s1, s2;
  int n11 = x.getN1(), n12 = x.getN2(), n21 = y.getN1(), n22 = y.getN2(), n1, n2;
  int b1 = inequalities[x.position()], b2 = inequalities[y.position()];
  // Case +/- x (...); -/+ x (...) 
  if(n11 == n21 && n11 == elim){
    // Case +/- x +/- y <= b1; -/+ x +/- y <= b2 
    if(s12 == s22 && n12 == n22){
      OctagonalFormula temp(s12, n12, '+', -1);
      inequalities[temp.position()] = std::min(inequalities[temp.position()], (b1 + b2)/2);
      updatePositions(temp);
      printMessage(fileOut, debug, x, y, temp);
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
      inequalities[temp.position()] = std::min(inequalities[temp.position()], b1 + b2);
      updatePositions(temp);
      printMessage(fileOut, debug, x, y, temp);
    }
  }
  // Case +/- x (...); (..) -/+ x (..)
  else if(n11 == n22 && n11 == elim){
    // Case +/- x +/- y <= b1; +/- y -/+ x <= b2
    if(s12 == s21 && n12 == n21){
      OctagonalFormula temp(s12, n12, '+', -1);	
      inequalities[temp.position()] = std::min(inequalities[temp.position()], (b1 + b2)/2);
      updatePositions(temp);
      printMessage(fileOut, debug, x, y, temp);
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
      inequalities[temp.position()] = std::min(inequalities[temp.position()], b1 + b2);
      updatePositions(temp);
      printMessage(fileOut, debug, x, y, temp);
    }
  }
  // Case (..) +/- x (..); -/+ x (...)
  else if(n12 == n21 && n12 == elim){
    // Case +/- y +/- x <= b1; -/+ x +/- y <= b2
    if(s11 == s22 && n11 == n22){
      OctagonalFormula temp(s11, n11, '+', -1);
      inequalities[temp.position()] = std::min(inequalities[temp.position()], (b1 + b2)/2);
      updatePositions(temp);
      printMessage(fileOut, debug, x, y, temp);
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
      inequalities[temp.position()] = std::min(inequalities[temp.position()], b1 + b2);
      updatePositions(temp);
      printMessage(fileOut, debug, x, y, temp);
    }
  }
  // Case (..) +/- x (..); (..) -/+ x (..)
  else if(n12 == n22 && n12 == elim){
    // Case +/- y +/- x <= b1; +/- y -/+ x <= b2
    if(s11 == s21 && n11 == n21){
      OctagonalFormula temp(s11, n11, '+', -1);
      inequalities[temp.position()] = std::min(inequalities[temp.position()], (b1 + b2)/2);
      updatePositions(temp);
      printMessage(fileOut, debug, x, y, temp);
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
      inequalities[temp.position()] = std::min(inequalities[temp.position()], b1 + b2);
      updatePositions(temp);
      printMessage(fileOut, debug, x, y, temp);
    }
  }
  //inequalities[position(x)] = INF;
  //inequalities[position(y)] = INF;
}

void Octagons::interpolation(std::ostream & os){
  int maxNumIneqs = 2*(numVar+1)*(numVar+1);
  if(debug){
    os << "Initial Inequalities:" << std::endl;
    for(int i = 0; i < maxNumIneqs; ++i)
      if(inequalities[i] != INF){
	OctagonalFormula(i).print(os);
	os << " <= " << inequalities[i] << std::endl;
      }
  }
  os << std::endl;

  // ----------------------------------------------------------------------------------------------------------------
  // Interpolation Algorithm
  for(vi::iterator it = variablesToEliminate.begin();
      it != variablesToEliminate.end();
      ++it){
    if(debug)
      os << "Eliminating variable x_" << *it << "\n";    

    for(vi::iterator x = pos[*it].begin(); x != pos[*it].end(); ++x){
      for(vi::iterator y = neg[*it].begin(); y != neg[*it].end(); ++y){
	if(inequalities[*x] != INF && inequalities[*y] != INF){
	  operate(os, *it, OctagonalFormula(*x), OctagonalFormula(*y));
	}
      }
    }
    
    for(vi::iterator x = pos[*it].begin(); x != pos[*it].end(); ++x)
      inequalities[*x] = INF;
    for(vi::iterator x = neg[*it].begin(); x != neg[*it].end(); ++x)
      inequalities[*x] = INF;

    if(debug){
      os << "After Eliminating Variable x_" << *it << "\n";
      for(int i = 0; i < maxNumIneqs; ++i)
	if(inequalities[i] != INF)
	  if(debug){
	    OctagonalFormula(i).print(os);
	    os << " <= " << inequalities[i] << "\n";
	  }
    }
  }
  // ----------------------------------------------------------------------------------------------------------------
}
