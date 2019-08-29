#include <iostream>
#include <fstream>
#include <cstdlib>
#include <ctime>

#include "EUFInterpolant.h"

int main(int argc, char ** argv){

  // Testing EUFInterpolant algorithm
  // std::string input_file = "./tests/smt2lib_2/kapurEUFExample.smt2";
  std::string input_file = "./tests/smt2lib_2/simple.smt2";
  // std::string input_file = "./tests/smt2lib_2/simple2.smt2";
  // std::string input_file = "./tests/smt2lib_2/kapurEUFExample2.smt2";
  // std::string input_file = "/Users/joseabelcastellanosjoo/Documents/QF_UF/2018-Goel-hwbench/QF_UF_firewire_tree.5.prop3_ab_reg_max.smt2";
  // std::string input_file = "/Users/joseabelcastellanosjoo/Documents/QF_UF/2018-Goel-hwbench/QF_UF_firewire_tree.3.prop2_ab_reg_max.smt2";
  // std::string input_file = "/Users/joseabelcastellanosjoo/Documents/QF_UF/2018-Goel-hwbench/QF_UF_needham.3.prop4_ab_reg_max.smt2";
  
  z3::context ctx;
  z3::expr input_formula = ctx.parse_file(input_file.c_str())[0];
  // std::cout << input_formula.arg(0).arg(1).decl().range().id() << std::endl;
  z3::sort sort_A = ctx.uninterpreted_sort("A");
  std::set<std::string> symbols_to_elim = {"f"};
  
  // Converter cvt (ctx, sort_A);
  // EUFInterpolant example (ctx, input_formula, symbols_to_elim, cvt);
  // std::cout << "The Interpolant" << std::endl;
  // std::cout << example.algorithm() << std::endl; 
  return 0;
}
