#include <iostream>
#include <fstream>
#include <cstdlib>
#include <ctime>
#include <string>

void generateInputFile(int & numTerms, int & numEqs, std::string & name){
  int lhs, rhs;
  int testQ;
  std::cout << "1. Generate new test\n";
  std::cout << "2. Work with previous test\n";
  std::cout << "Choose option: ";
  std::cin >> testQ;
  std::cout << "Input file name: ";
  std::cin >> name;
  if(testQ == 1){
    std::ofstream inputFile;
    srand(time(0));
    std::cout << "Number of terms: ";
    std::cin >> numTerms; 
    inputFile.open("tests/" + name);
    numEqs = rand() % numTerms;
    inputFile << std::to_string(numTerms) << " " << std::to_string(numEqs) << "\n";
    inputFile << "0 0\n1 0\n2 0\n3 0\n";
    for(int i = 4; i < numTerms; ++i){
      int numArgsTemp = 1 + rand() % 2;
      inputFile << i << " " << numArgsTemp << " ";
      while(numArgsTemp > 0){
	inputFile << rand() % i << " ";
	--numArgsTemp;
      }
      inputFile << "\n";
    }
    while(numEqs > 0){
      lhs = rand() % numTerms;
      rhs = rand() % numTerms;
      while(lhs == rhs)
	rhs = rand() % numTerms;
      inputFile << lhs << " " << rhs << "\n";
      --numEqs;
    }
    inputFile.close();
  }
}

void generateInputFile2(int & numTerms, int & numEqs, std::string & name){
  int lhs, rhs;
  std::ofstream inputFile;
  srand(time(0));
  inputFile.open("tests/" + name);
  numEqs = rand() % numTerms;
  inputFile << std::to_string(numTerms) << " " << std::to_string(numEqs) << "\n";
  inputFile << "0 0\n1 0\n2 0\n3 0\n";
  for(int i = 4; i < numTerms; ++i){
    int numArgsTemp = rand() % 4;
    int repetitionsTemp = rand() % 8;
    while(repetitionsTemp > 0){
      inputFile << i << " " << numArgsTemp << " ";
    while(numArgsTemp > 0){
      inputFile << rand() % i << " ";
      --numArgsTemp;
    }
    inputFile << "\n";
    }
  }
  while(numEqs > 0){
    lhs = rand() % numTerms;
    rhs = rand() % numTerms;
    while(lhs == rhs)
      rhs = rand() % numTerms;
    inputFile << lhs << " " << rhs << "\n";
    --numEqs;
  }
  inputFile.close();
}
