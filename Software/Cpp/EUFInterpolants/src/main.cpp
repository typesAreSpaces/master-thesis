#include <iostream>
#include <fstream>
#include <cstdlib>
#include <ctime>

#include "EUFInterpolant.h"

int main(int argc, char ** argv){

  // Testing EUFInterpolant algorithm
  // char const * input_file = "./tests/smt2lib_2/kapurEUFExample.smt2";
  char const * input_file = "./tests/smt2lib_2/simple.smt2";
  // char const * input_file = "./tests/smt2lib_2/simple2.smt2";
  // char const * input_file = "./tests/smt2lib_2/kapurEUFExample2.smt2";
  // char const * input_file = "/Users/joseabelcastellanosjoo/Documents/QF_UF/2018-Goel-hwbench/QF_UF_firewire_tree.5.prop3_ab_reg_max.smt2";
  // char const * input_file = "/Users/joseabelcastellanosjoo/Documents/QF_UF/2018-Goel-hwbench/QF_UF_firewire_tree.3.prop2_ab_reg_max.smt2";
  // char const * input_file = "/Users/joseabelcastellanosjoo/Documents/QF_UF/2018-Goel-hwbench/QF_UF_needham.3.prop4_ab_reg_max.smt2";
  
  z3::context ctx;
  // std::cout << input_formula.arg(0).arg(1).decl().range().id() << std::endl;
  std::set<std::string> symbols_to_elim = {"f"};

  // CongruenceClosure example(ctx, input_formula, symbols_to_elim);
  // example.merge(6, 8);
  // example.buildCongruenceClosure();
  
  // CongruenceClosure example2(ctx, input_formula, symbols_to_elim);
  // example.transferEqClassAndPreds(example2);
  // example.buildCongruenceClosure();
  
  EUFInterpolant test(ctx.parse_file(input_file)[0],
		      symbols_to_elim,
		      ctx.uninterpreted_sort("A"));
  std::cout << "The Interpolant" << std::endl;
  // std::cout << test.buildInterpolant() << std::endl;
  return 0;
}
