#include <iostream>
#include "TestCongruenceClosureExplain.h"

int main(int argc, char ** argv){

  z3::context ctx;
  TestCongruenceClosureExplain test(mk_and(ctx.parse_file(argv[1])));
  std::cout << test << std::endl;

  return 0;
}
