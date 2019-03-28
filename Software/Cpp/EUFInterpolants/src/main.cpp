#include <iostream>
#include <fstream>
#include <cstdlib>
#include <ctime>

#include "EUFInterpolant.h"
#include "Declarations.h"

int main(int argc, char ** argv){
	
  // Testing EUFInterpolant algorithm
  std::string file = "./tests/smt2lib_2/kapurEUFExample.smt2";
  //std::string file = "/Users/joseabelcastellanosjoo/Documents/QF_UF/2018-Goel-hwbench/QF_UF_firewire_tree.5.prop3_ab_reg_max.smt2";
  //std::string file = "/Users/joseabelcastellanosjoo/Documents/QF_UF/2018-Goel-hwbench/QF_UF_firewire_tree.3.prop2_ab_reg_max.smt2";
  //std::string file = "/Users/joseabelcastellanosjoo/Documents/QF_UF/2018-Goel-hwbench/QF_UF_needham.3.prop4_ab_reg_max.smt2";

  z3::config cfg;
  cfg.set("PROOF", true);
  cfg.set("MODEL", true);
  cfg.set("TRACE", false);
  z3::context ctx(cfg);
	
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
  std::set<std::string> symbols_to_elim = {"v"};
	
  EUFInterpolant a (ctx, input_formula, symbols_to_elim);
  a.algorithm();

  std::cout << "Wait wuttt?" << std::endl;
  auto b = a.getHornClauses();
  for(auto x : b)
	std::cout << *x << std::endl;

  // std::cout << std::endl;

  // API to obtain declarations
  // of formulas
  Declarations decls (ctx, input_formula_expr);
  std::cout << "Sort Declarations" << std::endl;
  decls.display_sort_decls(std::cout);
  std::cout << std::endl;
  std::cout << "Func Declarations" << std::endl;
  decls.display_func_decls(std::cout);

  std::cout << "Testing the new get functors" << std::endl;
  auto funs = decls.getFunctions();
  for(auto x : funs)
	std::cout << x.name() << std::endl;

  // Attempting to construct a formula using funs
  z3::sort _sort_2 = ctx.uninterpreted_sort("A");
  z3::expr x_2 = ctx.constant("x1", _sort_2);
  z3::expr f_x_x_2 = funs[1](x_2, x_2);
  std::cout << "Formula constructed from funs" << std::endl;
  std::cout << f_x_x_2 << std::endl;
  std::cout << Z3_get_ast_id(ctx, f_x_x_2) << std::endl;
  // It worked as expected
  
  // // ---------------------------------------------------------
  // // The following code shows how to construct
  // // new terms using the z3++ api. We notice
  // // the context does not allow symbol duplication
  // // Test used:
  // // "./tests/smt2lib_2/kapurEUFExample2_4.smt2"
  // // ---------------------------------------------------------
  // z3::sort _sort = ctx.uninterpreted_sort("A");
  // z3::expr x = ctx.constant("x1", _sort);
  // z3::func_decl f = z3::function("f", _sort, _sort, _sort);
  // z3::expr f_x_x = f(x, x);
  // std::cout << "Input formula\n";
  // std::cout << input_formula_expr << std::endl;
  // std::cout << x << std::endl;
  // // Obtaining the ids of the 'new expressions'
  // // show that the Z3 manager doesn't create a
  // // new node for them when they have already
  // // been created
  // std::cout << "Ids" << std::endl;
  // std::cout << Z3_get_ast_id(ctx, x) << std::endl;
  // std::cout << f_x_x << std::endl;
  // std::cout << Z3_get_ast_id(ctx, f_x_x) << std::endl;

  // // ---------------------------------------------------------
  // // The following code shows how to construct
  // // new terms using the z3++ api. We notice
  // // the context does not allow symbol duplication
  // // Test used:
  // // "./tests/smt2lib_2/kapurEUFExample2_5.smt2"
  // // ---------------------------------------------------------
  // z3::sort _sort = ctx.uninterpreted_sort("A");
  // z3::sort_vector _sorts(ctx);
  // _sorts.push_back(_sort), _sorts.push_back(_sort), _sorts.push_back(_sort);
  // z3::func_decl f  = z3::function("f", _sorts, _sort);
  // z3::expr x1 = ctx.constant("x1", _sort);
  // z3::expr f_x1_x1_x1 = f(x1, x1, x1);
  // z3::expr x2 = ctx.constant("x2", _sort);
  // z3::expr f_x1_x2_x1 = f(x1, x2, x1);

  // std::cout << f_x1_x1_x1 << std::endl;
  // std::cout << Z3_get_ast_id(ctx, f_x1_x1_x1) << std::endl;
  // std::cout << f_x1_x2_x1 << std::endl;
  // std::cout << Z3_get_ast_id(ctx, f_x1_x2_x1) << std::endl;
  // std::cout << x2 << std::endl;
  // std::cout << Z3_get_ast_id(ctx, x2) << std::endl;


  // // Example using substitution
  // // A Vector of (from) and a Vector of (to)
  // // are needed
  // z3::sort _sort = ctx.uninterpreted_sort("A");
  // z3::expr v = ctx.constant("v", _sort);
  // z3::expr w = ctx.constant("waaa", _sort);
  // z3::expr_vector v_vector(ctx);
  // z3::expr_vector w_vector(ctx);
  // w_vector.push_back(w);
  // v_vector.push_back(v);
  // std::cout << input_formula_expr << std::endl;
  // std::cout << input_formula_expr.substitute(v_vector, w_vector) << std::endl;
  
  return 0;
}
