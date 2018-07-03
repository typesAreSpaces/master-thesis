#include <iostream>
#include "hornsat.h"

int main(){
  // numDisPosLiterals = number of distinct positive literals in A
  // numBasicHornClauses = number of basic Horn Clauses in A
  int numDisPosLiterals, numBasicHornClauses;
  
  std::cin >> numDisPosLiterals >> numBasicHornClauses;
  Hornclause A = Hornclause(numDisPosLiterals, numBasicHornClauses);
  A.satisfiable();
  
  if(A.isConsistent()){
    std::cout << "Satisfiable Horn Clause" << std::endl;
    A.printAssignment();
  }
  else
    std::cout << "Unsatisfiable Horn Clause" << std::endl;
  
  return 0;
}
