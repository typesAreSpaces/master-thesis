#include <iostream>
#include "TestCongruenceClosureExplain.h"

int main(int argc, char ** argv){

  if(argc == 2){
    z3::context ctx;
    TestCongruenceClosureExplain test(mk_and(ctx.parse_file(argv[1])));
    //std::cout << test << std::endl;
    return 0;
  }
  return 1;
}
