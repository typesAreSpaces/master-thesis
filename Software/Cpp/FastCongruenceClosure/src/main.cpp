#include <iostream>
#include <fstream>
#include <cstdlib>
#include <ctime>

#include "CongruenceClosure.h"

int main(int argc, char ** argv){

  std::string file = "./tests/smt2lib/kapurEUFExample.smt2";
  //std::string file = "/Users/joseabelcastellanosjoo/Documents/QF_UF/2018-Goel-hwbench/QF_UF_firewire_tree.5.prop3_ab_reg_max.smt2";
  
  z3::config cfg;
  cfg.set("PROOF", true);
  cfg.set("MODEL", true);
  cfg.set("TRACE", false);
  z3::context ctx(cfg);

  Z3_ast inputFormula = Z3_parse_smtlib2_file(ctx, file.c_str(), 0, 0, 0, 0, 0, 0);
  //Z3_ast inputFormula = Z3_parse_smtlib2_file(ctx, argv[1], 0, 0, 0, 0, 0, 0);
  
  CongruenceClosure cc(ctx, inputFormula);
  cc.algorithm();
  cc.print(std::cout);
  if(cc.checkCorrectness())
    std::cout << "Success!" << std::endl;
  else
    std::cout << "There is a problem :(" << std::endl;
  return 0;
}

/*
#include "CongruenceClosure.h"
#include "produceRandomEqs.h"

int main(int argc, char ** argv){
  
  if(argc == 2){  
    std::ifstream file;
    file.open(argv[1], std::ifstream::in);
    
    CongruenceClosure cc = CongruenceClosure(file);
    file.close();
    //std::clock_t start = std::clock(); 
    cc.algorithm();
    //std::clock_t end = std::clock();
    //int numTerms = Vertex::getTotalNumVertex();
    //std::cout << numTerms << "," << (end - start)/(double)CLOCKS_PER_SEC << std::endl;
    cc.print(std::cout);
    if(cc.checkCorrectness())
      std::cout << "Success!" << std::endl;
    else
      std::cout << "There is a problem :(" << std::endl;
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
*/
