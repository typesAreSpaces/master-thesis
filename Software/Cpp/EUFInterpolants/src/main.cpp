#include <iostream>
#include <fstream>
#include <cstdlib>
#include <ctime>

#include "EUFInterpolant.h"

int main(int argc, char ** argv){
  
  if(argc >= 2) {
    z3::context ctx;
    z3::expr input_formula = ctx.parse_file(argv[1])[0];
    z3::expr aux_expr = input_formula;
    std::set<std::string> symbols_to_elim;
    for(int index = 2; index < argc; ++index)
      symbols_to_elim.insert(argv[index]);

    // Find a leave node in input_formula
    // in order to find the sort
    // of every expression (convention)
    while(aux_expr.num_args() != 0)
      aux_expr = aux_expr.arg(0);
    
    // CongruenceClosure cc_example(ctx, input_formula, symbols_to_elim, 0);
    // std::cout << cc_example << std::endl;
    // cc_example.addEquation(6, 11);
    // std::cout << cc_example << std::endl;

    // CongruenceClosure cc_example2(ctx, input_formula, symbols_to_elim, 1);
    // cc_example.transferEqClassAndPreds(cc_example2);
    // std::cout << cc_example << std::endl;
    
    EUFInterpolant euf_interpolant_example(input_formula,
    					   symbols_to_elim,
					   aux_expr.decl().range());
    euf_interpolant_example.test(); 
  }
  return 0;
}
