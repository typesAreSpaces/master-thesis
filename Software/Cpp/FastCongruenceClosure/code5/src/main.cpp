#include <iostream>
#include <fstream>
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
    cc.print(std::cout);
  }
  
  if(argc == 7){
    //generateFile(int numTest, int numConstantSyms, int numFunctionSyms, int numTerms, int numEqs)
    // ./main             9               4                  3                  20           4
    if(atoi(argv[6]) == 0)
      generateFile(atoi(argv[1]), atoi(argv[2]), atoi(argv[3]), atoi(argv[4]), atoi(argv[5]));
    
    if(atoi(argv[6]) == 1)
      generateFileAndTest(atoi(argv[1]), atoi(argv[2]), atoi(argv[3]), atoi(argv[4]), atoi(argv[5]));
  }  
  
  return 0;
}
