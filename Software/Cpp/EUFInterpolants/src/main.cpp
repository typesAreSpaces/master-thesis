#include <iostream>
#include <fstream>
#include <cstdlib>
#include <ctime>

#include "EUFInterpolant.h"

int main(int argc, char ** argv){
  // CongruenceClosure example(ctx, input_formula, symbols_to_elim);
  // example.merge(6, 8);
  // example.buildCongruenceClosure();
  
  // CongruenceClosure example2(ctx, input_formula, symbols_to_elim);
  // example.transferEqClassAndPreds(example2);
  // example.buildCongruenceClosure();

  if(argc >= 2) {
    z3::context ctx;
    std::set<std::string> symbols_to_elim;
    for(int index = 2; index < argc; ++index)
      symbols_to_elim.insert(argv[index]);
    // std::cout << input_formula.arg(0).arg(1).decl().range().id() << std::endl;
    EUFInterpolant test(ctx.parse_file(argv[1])[0],
			symbols_to_elim,
			ctx.uninterpreted_sort("A"));
    std::cout << "The Interpolant" << std::endl;
    // std::cout << test.buildInterpolant() << std::endl;
  }
  return 0;
}
