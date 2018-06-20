#include "interpolationOct.hpp"

void interpolationOct(std::ostream & fileOut,
		      inequalities & systemOfInequalities,
		      vi & variablesToEliminate,
		      positions & posPositions,
		      positions & negPositions,
		      int & numVar){

  int maxNumIneqs = 2*(numVar+1)*(numVar+1);
  if(debug){
    fileOut << "Initial Inequalities:" << "\n";
    for(int i = 0; i < maxNumIneqs; ++i){
      if(systemOfInequalities[i] != INF){
	invPosition(i).print(fileOut);
	fileOut << " <= " << systemOfInequalities[i] << std::endl;
      }
      fileOut << std::endl;
    }
  }    

  // ----------------------------------------------------------------------------------------------------------------
  // Interpolation Algorithm
  for(vi::iterator it = variablesToEliminate.begin();
      it != variablesToEliminate.end();
      ++it){
    if(debug)
      fileOut << "Eliminating variable x_" << *it << "\n";    

    for(vi::iterator x = posPositions[*it].begin(); x != posPositions[*it].end(); ++x){
      for(vi::iterator y = negPositions[*it].begin(); y != negPositions[*it].end(); ++y){
	if(systemOfInequalities[*x] != INF && systemOfInequalities[*y] != INF)
	  operate(fileOut, *it, invPosition(*x), invPosition(*y), systemOfInequalities, posPositions, negPositions);
      }
    }
    
    for(vi::iterator x = posPositions[*it].begin(); x != posPositions[*it].end(); ++x)
      systemOfInequalities[*x] = INF;
    for(vi::iterator x = negPositions[*it].begin(); x != negPositions[*it].end(); ++x)
      systemOfInequalities[*x] = INF;

    if(debug){
      fileOut << "After Eliminating Variable x_" << *it << "\n";
      for(int i = 0; i < maxNumIneqs; ++i)
	if(systemOfInequalities[i] != INF)
	  if(debug){
	    invPosition(i).print(fileOut);
	    fileOut << " <= " << systemOfInequalities[i] << "\n";
	  }
    }
  }
  // ----------------------------------------------------------------------------------------------------------------
}
