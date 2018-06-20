#include <iostream>
#include <fstream>
#include "structures.hpp"
#include "readFile.hpp"
#include "generateTest.hpp"
#include "interpolationOct.hpp"
#include "testSolution.hpp"

int main(int argc, char ** argv){

  // -----------------------------------------------------
  // DEFS from structures.hpp
  inequalities systemOfInequalities (MAX_NUM_INEQS, INF);
  positions posPositions (MAX_NUM_VARS);
  positions negPositions (MAX_NUM_VARS);
  // -----------------------------------------------------
  vi variablesToEliminate;
  int numVar, whatToDo, whereToWrite;
  std::string fileName;
  std::ifstream fileIn;
  std::ofstream fileOut;
  
  std::cout << "What to do?" << std::endl;
  std::cout << "1.Compute Interpolant from Random Test" << std::endl;
  std::cout << "2.Compute Interpolant from File" << std::endl;
  std::cout << "3.Check consistency and correctness of Algorithm from Random Test" << std::endl;
  std::cout << "4.Check consistency and correctness of Algorithm from File" << std::endl;
  std::cin >> whatToDo;
  std::cout << "Where to store results?" << std::endl;
  std::cout << "1. std::cout" << std::endl;
  std::cout << "2. fileOut" << std::endl;
  std::cin >> whereToWrite;

  switch(whatToDo){
  case 1:
    // Creates file with test
    fileName = generate();

    // Reads Input from file
    fileIn.open("tests/" + fileName + ".in");
    readInput(fileIn, systemOfInequalities, variablesToEliminate, posPositions, negPositions, numVar);
    fileIn.close();

    // Generates interpolant and prints results
    switch(whereToWrite){
    case 1:
      interpolationOct(std::cout, systemOfInequalities, variablesToEliminate, posPositions, negPositions, numVar);
      break;
    case 2:
      fileOut.open("results/" + fileName + ".out");
      interpolationOct(fileOut, systemOfInequalities, variablesToEliminate, posPositions, negPositions, numVar);
      fileOut.close();
      break;
    default:
      break;
    }
    std::cout << "Produced file: " << fileName << std::endl;
    break;
    
  case 2:
    // Reads from a given file
    std::cout << "Name of the file: ";
    std::cin >> fileName;
      
    // Reads Input from file
    fileIn.open("tests/" + fileName + ".in");
    readInput(fileIn, systemOfInequalities, variablesToEliminate, posPositions, negPositions, numVar);
    fileIn.close();
    
    // Generates interpolant and prints results
    switch(whereToWrite){
    case 1:
      interpolationOct(std::cout, systemOfInequalities, variablesToEliminate, posPositions, negPositions, numVar);
      break;
    case 2:
      fileOut.open("results/" + fileName + ".out");
      interpolationOct(fileOut, systemOfInequalities, variablesToEliminate, posPositions, negPositions, numVar);
      fileOut.close();
      break;
    default:
      break;
    }
    break;
    
  case 3:
    // Creates file with test
    fileName = generate();

    // Reads Input from file
    fileIn.open("tests/" + fileName + ".in");
    readInput(fileIn, systemOfInequalities, variablesToEliminate, posPositions, negPositions, numVar);
    fileIn.close();
    
    switch(whereToWrite){
    case 1:
      testSolution(std::cout, systemOfInequalities, variablesToEliminate, posPositions, negPositions, numVar);
      break;
    case 2:
      fileOut.open("results/" + fileName + ".out");
      testSolution(fileOut, systemOfInequalities, variablesToEliminate, posPositions, negPositions, numVar);
      fileOut.close();
      break;
    default:
      break;
    }
    break;

  case 4:
    // Reads from a given file
    std::cout << "Name of the file: ";
    std::cin >> fileName;

    // Reads Input from file
    fileIn.open("tests/" + fileName + ".in");
    readInput(fileIn, systemOfInequalities, variablesToEliminate, posPositions, negPositions, numVar);
    fileIn.close();
    
    switch(whereToWrite){
    case 1:
      testSolution(std::cout, systemOfInequalities, variablesToEliminate, posPositions, negPositions, numVar);
      break;
    case 2:
      fileOut.open("results/" + fileName + ".out");
      testSolution(fileOut, systemOfInequalities, variablesToEliminate, posPositions, negPositions, numVar);
      fileOut.close();
      break;
    default:
      break;
    }
    break;
    
  default:
    break;
  }
  
  return 0;
}
