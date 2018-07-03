#include <iostream>
#include <fstream>
#include "hornsat.h"

int main(int argc, char ** argv){
  
  Hornclause * A;
  
  if(argc == 2){
    std::ifstream file;
    file.open(argv[1], std::ifstream::in);
    A = new Hornclause(file);
    file.close();
  }
  else if(argc == 1)
    A = new Hornclause(std::cin);
  else
    return 0;
  
  A->satisfiable();
  
  if(A->isConsistent()){
    std::cout << "Satisfiable Horn Clause" << std::endl;
    A->printAssignment(std::cout);
  }
  else
    std::cout << "Unsatisfiable Horn Clause" << std::endl;

  delete A;
  
  return 0;
}
