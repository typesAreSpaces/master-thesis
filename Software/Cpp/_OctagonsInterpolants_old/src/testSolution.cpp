#include "testSolution.hpp"

void testSolution(std::ostream & fileOut,
		  inequalities & systemOfInequalities,
		  vi & variablesToEliminate,
		  positions & posPositions,
		  positions & negPositions,
		  int & numVar){
  int maxNumIneqs = 2*(numVar+1)*(numVar+1), test;
  
  srand(time(NULL));
  bool value = true, value2 = true, value3 = true;
  vi assignments (numVar + 1);
  for (vi::iterator it = assignments.begin();
       it != assignments.end();
       ++it){
    *it = rand() % 100 - 50;
  }

  // Checks satisfiability for the original set of octagonal formulas
  for(int i = 0; i < maxNumIneqs; ++i){
    if(systemOfInequalities[i] != INF){
      OctagonalFormula temp = invPosition(i);
      if(temp.s1 == '+')
	test = temp.n1;
      else
	test = -temp.n1;
      if(temp.s2 == '+')
	test += temp.n2;
      else
	test -= temp.n2;
      if(test > systemOfInequalities[i])
	value = false;
    }
  }  

  interpolationOct(fileOut, systemOfInequalities, variablesToEliminate, posPositions, negPositions, numVar);

  // Checks satisfiability for the new set of octagonal formulas
  for(int i = 0; i < maxNumIneqs; ++i){
    if(systemOfInequalities[i] != INF){
      OctagonalFormula temp = invPosition(i);
      if(temp.s1 == '+')
	test = temp.n1;
      else
	test = -temp.n1;
      if(temp.s2 == '+')
	test += temp.n2;
      else
	test -= temp.n2;
      if(test > systemOfInequalities[i])
	value2 = false;
    }
  }

  for(vi::iterator it = variablesToEliminate.begin();
      it != variablesToEliminate.end();
      ++it){
    for(int i = 0; i < maxNumIneqs; ++i){
      if(systemOfInequalities[i] != INF){
	OctagonalFormula temp = invPosition(i);
	if(temp.n1 == *it || temp.n2 == *it){
	  value3 = false;
	  break;
	}
      }
    }
  }

  fileOut << "Satifiability Original Formulas: " << value << std::endl;
  fileOut << "Satifiability New Formulas: " << value2 << std::endl;
  fileOut << "Remove all variables to eliminate?: " << (value3 ? "Yes" : "No") << std::endl;
							     
}
