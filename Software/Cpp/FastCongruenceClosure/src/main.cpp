#include <iostream>
#include <fstream>
#include <cstdlib>
#include "GTerms.h"
#include "SignatureTable.h"
#include "CongruenceClosure.h"
#include "produceRandomEqs.h"
#include <ctime>

int main(int argc, char ** argv){

  if(argc == 2){  
    std::ifstream file;
    file.open(argv[1], std::ifstream::in);
    
    GTerms terms = GTerms(file);
    SignatureTable sigTable = SignatureTable(terms);
    CongruenceClosure cc = CongruenceClosure(terms, sigTable, file);
    file.close();
    //std::clock_t start = std::clock(); 
    cc.algorithm();
    //std::clock_t end = std::clock();
    //int numTerms = Vertex::getTotalNumVertex();
    //std::cout << numTerms << "," << (end - start)/(double)CLOCKS_PER_SEC << std::endl;
    cc.print(std::cout);
    checkCorrectness(terms, sigTable);
  }
  if(argc == 7){
    // void generateFile(int numTest, int numConstantSyms, int numFunctionSyms, int numTerms, int numEqs){
    if(atoi(argv[6]) == 0)
      generateFile(atoi(argv[1]), atoi(argv[2]), atoi(argv[3]), atoi(argv[4]), atoi(argv[5]));
    
    if(atoi(argv[6]) == 1)
      generateFileAndTest(atoi(argv[1]), atoi(argv[2]), atoi(argv[3]), atoi(argv[4]), atoi(argv[5]));
  }

  // Checking Performance
  if(argc == 1)
    for(int i = 10; i < 100000; i += 100){   
      // =-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-
      // Pararemeters 
      int numTest = 2, numConstantSyms = 3, numFunctionSyms = 4,
	numTerms = i, numEqs = rand() % i + 1;
      // =-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-
      worstCaseFileAndTest(numTest, numConstantSyms, numFunctionSyms, numTerms, numEqs);
    }
  
  return 0;
}
