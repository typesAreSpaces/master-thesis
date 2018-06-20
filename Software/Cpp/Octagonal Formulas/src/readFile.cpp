#include "readFile.hpp"

void readInput(std::istream & file,
	       inequalities & systemOfInequalities,
	       vi & variablesToEliminate,
	       positions & posPositions,
	       positions & negPositions,
	       int & numVar){

  numVar = -1;
  int n1, n2, b, n, maxNumIneqs;
  char s1, s2;

  for(inequalities::iterator it = systemOfInequalities.begin();
      it != systemOfInequalities.end();
      ++it){
    *it = INF;
  }
  
  // ----------------------------------------------------------------
  // Getting the number of inequalities  
  file >> n;
    
  while(n > 0){
    file >> s1 >> n1 >> s2 >> n2 >> b;
    OctagonalFormula temp(s1, n1, s2, n2);
    // -----------------------------------
    // Normalization
    temp = normal(temp, b);
    // -----------------------------------
    updatePositions(temp, posPositions, negPositions);
    if(n1 > numVar)
      numVar = n1;
    if(n2 > numVar)
      numVar = n2;
    systemOfInequalities[temp.position()] =
      std::min(systemOfInequalities[temp.position()], b);
    n--;
  }
  // ----------------------------------------------------------------

  // ----------------------------------------------------------------
  // Getting the number of variables to eliminate
  file >> n;
  while(n > 0){
    file >> n1;
    variablesToEliminate.push_back(n1);
    n--;
  }
  // ----------------------------------------------------------------
  
}
