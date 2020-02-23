#include <iostream>
#include <fstream>
#include "Hornsat.h"

int main(int argc, char ** argv){
  
  Hornsat * A;
  
  if(argc == 2){
    std::ifstream file;
    file.open(argv[1], std::ifstream::in);
    A = new Hornsat(file);
    file.close();
  }
  else if(argc == 1)
    A = new Hornsat(std::cin);
  else
    return 0;
  
  A->satisfiable();
  
  if(A->isConsistent()){
    std::cout << "Satisfiable Horn Clause" << std::endl;
    std::cout << *A << std::endl;
  }
  else
    std::cout << "Unsatisfiable Horn Clause" << std::endl;
  
  delete A;
  
  return 0;
}
