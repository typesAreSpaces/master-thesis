#include "generateTest.h"

std::string generate(){

  srand(time(NULL));

  // DEFS obtained from generateTest.hpp
  int i, sign,
    numberOfInequalities = rand() % MAX_NUM_INEQUALITIES_RAND + 100,
    numOfVars = rand() % MAX_NUM_VARS_RAND + 20,
    numberOfElimVariables = rand() % MAX_NUM_ELIM_RAND + 1;

  std::string fileName = "example_"
    + std::to_string(numberOfInequalities) + "_"
    + std::to_string(numOfVars) + "_"
    + std::to_string(numberOfElimVariables);
  std::ofstream file;
  file.open("tests/" + fileName + ".in");
  
  file << numberOfInequalities << std::endl;
  for(i = 0; i < numberOfInequalities; ++i){
    sign = rand() % 1000;
    if(sign % 2)
      file << "+ ";
    else
      file << "- ";
    
    // Important +1 since we reversed x_0 for constants
    file << rand() % numOfVars + 1; 
    sign = rand() % 1000;
    if(sign % 2)
      file << " + ";
    
    else
      file << " - ";
    
    // Important +1 since we reversed x_0 for constants
    file << rand() % numOfVars + 1 << " " << rand() % 100 - 50 << std::endl;    
  }

  file << numberOfElimVariables << std::endl;
  for(i = 0; i < numberOfElimVariables; ++i){
    // Important +1 since we reversed x_0 for constants
    file << rand() % numOfVars + 1 << " ";
  }

  file << std::endl;
  file.close();
  return fileName;
}
