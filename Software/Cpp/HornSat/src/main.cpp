#include <iostream>
#include <fstream>
#include "Hornsat.h"

void checkSatisfiability(Hornsat & A){
  A.satisfiable();
  
  if(A.isConsistent()){
    std::cout << "Satisfiable Horn Clause" << std::endl;
    std::cout << A << std::endl;
  }
  else
    std::cout << "Unsatisfiable Horn Clause" << std::endl;  
}

int main(int argc, char ** argv){

  switch(argc){
  case 1:{
    Hornsat A(std::cin);
    checkSatisfiability(A);
    return 0;
  }
  case 2:{
    std::ifstream file;
    file.open(argv[1]);
    Hornsat A(file);
    checkSatisfiability(A);
    file.close();
    return 0;
  }
  default:
    return 1;
  }
}
