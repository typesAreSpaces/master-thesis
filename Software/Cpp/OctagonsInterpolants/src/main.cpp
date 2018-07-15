#include <iostream>
#include <fstream>
#include "Octagons.h"

int main(int argc, char ** argv){
  if(argc == 2){
    std::ifstream file;
    file.open(argv[1], std::ifstream::in);

    Octagons oc = Octagons(file);
    oc.interpolation(std::cout);
  }
  return 0;
}
