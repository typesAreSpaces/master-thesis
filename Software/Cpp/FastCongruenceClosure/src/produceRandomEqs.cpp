#include "produceRandomEqs.h"

void generateFile(unsigned numTest, unsigned numConstantSyms, unsigned numFunctionSyms, unsigned numTerms, unsigned numEqs){
  //system("mkdir tests");
  unsigned counter;
  char _temp;
  std::string fileName;
  std::ofstream file;
  std::string directoryName = "tests/test_"
    + std::to_string(numTest) + "_"
    + std::to_string(numConstantSyms) + "_"
    + std::to_string(numFunctionSyms) + "_"
    + std::to_string(numTerms) + "_"
    + std::to_string(numEqs);
  system(("mkdir " + directoryName).c_str());

  std::map<char, unsigned> arities;
  for(unsigned i = 0; i < numFunctionSyms; ++i)
    arities.insert(std::make_pair((char) ('f' + i), rand() % 4 + 1));
  
  for(unsigned i = 0; i < numTest; ++i){
    fileName = directoryName + "/" + std::to_string(i) + ".txt";
    file.open(fileName);
    // -------------------------------------------------------------
    // Writing on the file!
    counter = 0;
    file << (numConstantSyms + numTerms) << std::endl;
    for(unsigned j = 0; j < numConstantSyms; ++j){
      file << (char)('a' + j) << " 0" << std::endl;
      ++counter;
    }
    for(unsigned j = 0; j < numTerms; ++j){
      _temp = (char)('f' + rand() % numFunctionSyms);
      file << _temp << " " << arities[_temp];
      for(unsigned k = 0; k < arities[_temp]; ++k)
	file << " " << rand() % counter;
      file << std::endl;
      ++counter;
    }
    file << numEqs << std::endl;
    for(unsigned i = 0; i < numEqs; ++i)
      file << (rand() % counter) << " " << (rand() % counter) << std::endl;
    // -------------------------------------------------------------
    file.close();
  }   
}

void generateFileAndTest(unsigned numTest, unsigned numConstantSyms, unsigned numFunctionSyms, unsigned numTerms, unsigned numEqs){
  generateFile(numTest, numConstantSyms, numFunctionSyms, numTerms, numEqs);
  run(numTest, numConstantSyms, numFunctionSyms, numTerms, numEqs);
}

void worstCaseFile(unsigned numTest, unsigned numConstantSyms, unsigned numFunctionSyms, unsigned numTerms, unsigned numEqs){
  //system("mkdir tests");
  unsigned counter;
  char _temp;
  std::string fileName;
  std::ofstream file;
  std::string directoryName = "tests/test_"
    + std::to_string(numTest) + "_"
    + std::to_string(numConstantSyms) + "_"
    + std::to_string(numFunctionSyms) + "_"
    + std::to_string(numTerms) + "_"
    + std::to_string(numEqs);
  system(("mkdir " + directoryName).c_str());

  std::map<char, unsigned> arities;
  for(unsigned i = 0; i < numFunctionSyms; ++i)
    arities.insert(std::make_pair((char) ('f' + i), rand() % 4 + 1));
  
  for(unsigned i = 0; i < numTest; ++i){
    fileName = directoryName + "/" + std::to_string(i) + ".txt";
    file.open(fileName);
    // -------------------------------------------------------------
    // Writing on the file!
    counter = 0;
    file << (numConstantSyms + numTerms) << std::endl;
    for(unsigned j = 0; j < numConstantSyms; ++j){
      file << (char)('a' + j) << " 0" << std::endl;
      ++counter;
    }
    for(unsigned j = 0; j < numTerms; ++j){
      _temp = (char)('f' + rand() % numFunctionSyms);
      file << _temp << " " << arities[_temp];
      for(unsigned k = 0; k < arities[_temp]; ++k)
	file << " " << rand() % counter;
      file << std::endl;
      ++counter;
    }
    // Making the hardest case
    file << numEqs << std::endl;
    for(unsigned i = 0; i < (numConstantSyms + numTerms) - 1; ++i)
      file << i << " " << (i + 1) << std::endl;
    // -------------------------------------------------------------
    file.close();
  }
}

void worstCaseFileAndTest(unsigned numTest, unsigned numConstantSyms, unsigned numFunctionSyms, unsigned numTerms, unsigned numEqs){
  worstCaseFile(numTest, numConstantSyms, numFunctionSyms, numTerms, numEqs);
  run(numTest, numConstantSyms, numFunctionSyms, numTerms, numEqs);
}

void run(unsigned numTest, unsigned numConstantSyms, unsigned numFunctionSyms, unsigned numTerms, unsigned numEqs){
  std::string directoryName = "tests/test_"
    + std::to_string(numTest) + "_"
    + std::to_string(numConstantSyms) + "_"
    + std::to_string(numFunctionSyms) + "_"
    + std::to_string(numTerms) + "_"
    + std::to_string(numEqs);
  for(unsigned i = 0; i < numTest; ++i)    
    system(("./main " + directoryName + "/" + std::to_string(i) + ".txt").c_str());
  //system("rm -r tests/test*");
}
