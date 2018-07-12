#include <iostream>
#include <fstream>
#include "GTerms.h"
#include "SignatureTable.h"
#include "CongruenceClosure.h"

int main(int argc, char ** argv){
 
  std::ifstream file;
  file.open(argv[1], std::ifstream::in);
  
  GTerms terms = GTerms(file);
  SignatureTable sigTable = SignatureTable(terms);
  CongruenceClosure cc = CongruenceClosure(terms, sigTable, file);
  file.close();
  
  cc.algorithm();
  cc.print(std::cout);
  
  return 0;
}
