#include <iostream>
#include <fstream>
#include <cstdlib>
#include "Vertex.h"
#include "GTerms.h"
#include "SignatureTable.h"
#include "CongruenceClosure.h"
#include "produceRandomEqs.h"

int main(int argc, char ** argv){

  if(argc == 2){  
    std::ifstream file;
    file.open(argv[1], std::ifstream::in);
  
    GTerms terms = GTerms(file);
    SignatureTable sigTable = SignatureTable(terms);
    CongruenceClosure cc = CongruenceClosure(terms, sigTable, file);
    file.close();
  
    cc.algorithm();
    bool check = true;
    for(int i = 0; i < Vertex::getTotalNumVertex() - 1; ++i){
      for(int j = i + 1; j < Vertex::getTotalNumVertex(); ++j){
	Vertex * u = terms.getTerm(i), * v = terms.getTerm(j);
	if(u->getArity() == v->getArity()){
	  if(u->getArity() == 1){
	    if(sigTable.getSignatureArg1(u) == sigTable.getSignatureArg1(v) && terms.find(u)->getId() != terms.find(v)->getId())
	      check = false;
	  }
	  if(u->getArity() == 2){
	    if(sigTable.getSignatureArg2(u) == sigTable.getSignatureArg2(v) && terms.find(u)->getId() != terms.find(v)->getId())
	      check = false;
	  }
	}
      }
    }

    if(check)
      std::cout << "Success!" << std::endl;
    else
      std::cout << "There is a problem :(" << std::endl;
    
    //cc.print(std::cout);
  }
  
  if(argc == 7){
    //generateFile(int numTest, int numConstantSyms, int numFunctionSyms, int numTerms, int numEqs)
    // ./main             9               4                  3                  20           4

    if(atoi(argv[6]) == 0)
      generateFile(atoi(argv[1]), atoi(argv[2]), atoi(argv[3]), atoi(argv[4]), atoi(argv[5]));
    
    if(atoi(argv[6]) == 1)
      generateFileAndTest(atoi(argv[1]), atoi(argv[2]), atoi(argv[3]), atoi(argv[4]), atoi(argv[5]));
  }

  if(argc == 1){
    float averageTime;
    for(int i = 10; i < 100; i += 10){
      
      // =-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-
      // Pararemeters 
      int numTest = 1, numConstantSyms = 1, numFunctionSyms = 1,
	numTerms = i, numEqs = rand() % i + 1;
      // =-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-
      
      generateFileAndTest(numTest, numConstantSyms, numFunctionSyms, numTerms, numEqs);
      /*
      averageTime = generateFileAndTest(numTest, numConstantSyms, numFunctionSyms, numTerms, numEqs);
      std::cout << numTest << " " << numConstantSyms << " " << numFunctionSyms
		<< " " << numTerms << " " << numEqs << " " << averageTime << std::endl;
      */
    }
  }
  
  return 0;
}
