#include <iostream>
#include <algorithm>
#include "Rename.h"
#include "EUFInterpolant.h"

void testFilePath(const char *);

int main(int argc, char ** argv){

  testFilePath(argv[1]);

  return 0;
}

void testFilePath(const char * smt_file){
  z3::context ctx;
  z3::expr input = mk_and(ctx.parse_file(smt_file));
  EUFInterpolant euf(input);
  //std::cout << euf << std::endl;
}

