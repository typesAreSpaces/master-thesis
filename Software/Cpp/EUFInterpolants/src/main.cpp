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
    z3::expr input_formula = ctx.parse_file(argv[1])[0];

    // std::cout << input_formula.arg(0).arg(1).decl().range().id() << std::endl;
    
    CongruenceClosure cc_example(ctx, input_formula, symbols_to_elim, 0);
    std::cout << cc_example << std::endl;
    cc_example.addEquation(6, 11);
    std::cout << cc_example << std::endl;

    CongruenceClosure cc_example2(ctx, input_formula, symbols_to_elim, 1);
    cc_example.transferEqClassAndPreds(cc_example2);
    std::cout << cc_example << std::endl;
    
    // EUFInterpolant euf_interpolant_example(input_formula,
    // 					   symbols_to_elim,
    // 					   ctx.uninterpreted_sort("A"));
    // std::cout << "The Interpolant" << std::endl;
    // euf_interpolant_example.test(); 
  }
  return 0;
}
