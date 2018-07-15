#include "produceRandomEqs.h"

void generateFile(int numTest, int numConstantSyms, int numFunctionSyms, int numTerms, int numEqs){
  system("mkdir tests");
  int counter;
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

  std::map<char, int> arities;
  for(int i = 0; i < numFunctionSyms; ++i)
    arities.insert(std::make_pair((char) ('f' + i), rand() % 4 + 1));
  
  for(int i = 0; i < numTest; ++i){
    fileName = directoryName + "/" + std::to_string(i) + ".txt";
    file.open(fileName);
    // -------------------------------------------------------------
    // Writing on the file!
    counter = 0;
    file << (numConstantSyms + numTerms) << std::endl;
    for(int j = 0; j < numConstantSyms; ++j){
      file << (char)('a' + j) << " 0" << std::endl;
      ++counter;
    }
    for(int j = 0; j < numTerms; ++j){
      _temp = (char)('f' + rand() % numFunctionSyms);
      file << _temp << " " << arities[_temp];
      for(int k = 0; k < arities[_temp]; ++k)
	file << " " << rand() % counter;
      file << std::endl;
      ++counter;
    }
    file << numEqs << std::endl;
    for(int i = 0; i < numEqs; ++i)
      file << (rand() % counter) << " " << (rand() % counter) << std::endl;
    // -------------------------------------------------------------
    file.close();
  }   
}

void generateFileAndTest(int numTest, int numConstantSyms, int numFunctionSyms, int numTerms, int numEqs){
  generateFile(numTest, numConstantSyms, numFunctionSyms, numTerms, numEqs);
  run(numTest, numConstantSyms, numFunctionSyms, numTerms, numEqs);
}

void worstCaseFile(int numTest, int numConstantSyms, int numFunctionSyms, int numTerms, int numEqs){
  system("mkdir test");
  int counter;
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

  std::map<char, int> arities;
  for(int i = 0; i < numFunctionSyms; ++i)
    arities.insert(std::make_pair((char) ('f' + i), rand() % 4 + 1));
  
  for(int i = 0; i < numTest; ++i){
    fileName = directoryName + "/" + std::to_string(i) + ".txt";
    file.open(fileName);
    // -------------------------------------------------------------
    // Writing on the file!
    counter = 0;
    file << (numConstantSyms + numTerms) << std::endl;
    for(int j = 0; j < numConstantSyms; ++j){
      file << (char)('a' + j) << " 0" << std::endl;
      ++counter;
    }
    for(int j = 0; j < numTerms; ++j){
      _temp = (char)('f' + rand() % numFunctionSyms);
      file << _temp << " " << arities[_temp];
      for(int k = 0; k < arities[_temp]; ++k)
	file << " " << rand() % counter;
      file << std::endl;
      ++counter;
    }
    file << numEqs << std::endl;
    for(int i = 0; i < (numConstantSyms + numTerms) - 1; ++i)
      file << i << " " << (i + 1) << std::endl;
    // -------------------------------------------------------------
    file.close();
  }
}

void worstCaseFileAndTest(int numTest, int numConstantSyms, int numFunctionSyms, int numTerms, int numEqs){
  worstCaseFile(numTest, numConstantSyms, numFunctionSyms, numTerms, numEqs);
  run(numTest, numConstantSyms, numFunctionSyms, numTerms, numEqs);
}

void run(int numTest, int numConstantSyms, int numFunctionSyms, int numTerms, int numEqs){
  std::string directoryName = "tests/test_"
    + std::to_string(numTest) + "_"
    + std::to_string(numConstantSyms) + "_"
    + std::to_string(numFunctionSyms) + "_"
    + std::to_string(numTerms) + "_"
    + std::to_string(numEqs);
  for(int i = 0; i < numTest; ++i){
    std::clock_t time_begin = std::clock();
    system(("./main " + directoryName + "/" + std::to_string(i) + ".txt").c_str());
    std::clock_t time_end = std::clock();
    std::cout << numTest << ", " << numConstantSyms << ", " << numFunctionSyms
	      << ", " << numTerms << ", " << numEqs << ", "
	      << ((time_end - time_begin)/(double)CLOCKS_PER_SEC) << std::endl;
  }
  system("rm -r tests/test*");
}

void checkCorrectness(GTerms & terms, SignatureTable & sigTable){
  bool check = true;
  for(int i = 0; i < Vertex::getTotalNumVertex() - 1; ++i)
    for(int j = i + 1; j < Vertex::getTotalNumVertex(); ++j){
      Vertex * u = terms.getTerm(i), * v = terms.getTerm(j);
      if(u->getArity() == v->getArity()){
	if(u->getArity() == 1){
	  if(sigTable.getSignatureArg1(u) == sigTable.getSignatureArg1(v) && terms.find(u)->getId() != terms.find(v)->getId())
	    check = false;
	}
	if(u->getArity() == 2)
	  if(sigTable.getSignatureArg2(u) == sigTable.getSignatureArg2(v) && terms.find(u)->getId() != terms.find(v)->getId())
	    check = false;
      }
    }
  if(check)
    std::cout << "Success!" << std::endl;
  else
    std::cout << "There is a problem :(" << std::endl;
}
