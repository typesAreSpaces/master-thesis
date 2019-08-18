#include <iostream>
#include <fstream>
#include <cstdlib>
#include <ctime>

#include "EUFInterpolant.h"
#include "Declarations.h"
#include "ConvertReprToZ3.h" 

int main(int argc, char ** argv){

  z3::config cfg;
  cfg.set("PROOF", true);
  cfg.set("MODEL", true);
  cfg.set("TRACE", false);
  z3::context ctx(cfg);
  z3::sort sort_A = ctx.uninterpreted_sort("A");
  
  // Testing EUFInterpolant algorithm
  std::string file = "./tests/smt2lib_2/kapurEUFExample.smt2";
  // std::string file = "./tests/smt2lib_2/kapurEUFExample2.smt2";
  // std::string file = "/Users/joseabelcastellanosjoo/Documents/QF_UF/2018-Goel-hwbench/QF_UF_firewire_tree.5.prop3_ab_reg_max.smt2";
  // std::string file = "/Users/joseabelcastellanosjoo/Documents/QF_UF/2018-Goel-hwbench/QF_UF_firewire_tree.3.prop2_ab_reg_max.smt2";
  // std::string file = "/Users/joseabelcastellanosjoo/Documents/QF_UF/2018-Goel-hwbench/QF_UF_needham.3.prop4_ab_reg_max.smt2";
  
  // I'm using Z3_ast_vector_get
  // because parsing from a file using 
  // Z3, the API only provides 
  // the function Z3_parse_smtlib2_file
  // which returns a Z3_ast_vector
  Z3_ast_vector conjunction_of_assertions =
  	Z3_parse_smtlib2_file(ctx, file.c_str(), 0, 0, 0, 0, 0, 0);
  Z3_ast input_formula =
  	Z3_ast_vector_get(ctx, conjunction_of_assertions, 0);
  z3::expr input_formula_expr(ctx, input_formula);
  std::set<std::string> symbols_to_elim = {"f"};
  
  Converter cvt (ctx, sort_A);
  EUFInterpolant example (ctx, input_formula, symbols_to_elim, cvt);
  std::cout << "The Interpolant" << std::endl;
  std::cout << example.algorithm() << std::endl; 


  CircularList<int> a;
  CircularList<int> b;

  for(int i = 0; i < 100; ++i){
    a.add(i);
    b.add(2*i);
  }
  
  std::cout << "List a: "<< a << std::endl;
  std::cout << std::endl;
  std::cout << "List b: " << b << std::endl;

  std::cout << std::endl;

  a.merge(b);
  
  std::cout << "List a: "<< a << std::endl;
  std::cout << std::endl;
  std::cout << "List b: " << b << std::endl;
  return 0;
}
