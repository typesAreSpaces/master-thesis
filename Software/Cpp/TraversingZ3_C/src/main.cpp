/*++
  Copyright (c) 2015 Microsoft Corporation

  --*/

#include "z3++.h"
#include "z3.h" 
#include "util.h"
#include "traversal.h"
#include "constructors.h"
#include "api_util.h"
#include <set>

int main(int argc, char ** argv) {

  std::string file = "./SMT2_files/interpolantExample2.smt2";
  //std::string file = "./SMT2_files/proveExample1a.smt2";
  //std::string file = "./SMT2_files/interpolantKapurExample1.smt2";
  //std::string file = "/Users/joseabelcastellanosjoo/Documents/QF_UF/2018-Goel-hwbench/QF_UF_firewire_tree.1.prop1_ab_cti_max.smt2";
  //std::string file = "/Users/joseabelcastellanosjoo/Documents/QF_UF/2018-Goel-hwbench/QF_UF_firewire_tree.5.prop3_ab_reg_max.smt2";
  
  z3::config cfg;
  cfg.set("PROOF", true);
  cfg.set("MODEL", true);
  cfg.set("TRACE", true);
  z3::context ctx(cfg);
  
  Z3_ast inputFormula = Z3_parse_smtlib2_file(ctx, (Z3_string)file.c_str(), 0, 0, 0, 0, 0, 0);
  
  std::set<int> counter;
  visit(ctx, stdout, inputFormula, counter);
  
  // This now works!, by including "api_util.h" of course
  //std::cout << to_expr(inputFormula)->get_ref_count() << std::endl;  
  std::cout << "The size counted by the set " << counter.size() << std::endl;
  
  Z3_goal g = Z3_mk_goal(ctx, true, false, false);
  Z3_goal_assert(ctx, g, inputFormula);
  std::cout << "The size counted by the goal procedure: " << Z3_goal_num_exprs(ctx, g) << std::endl;
  
  
  return 0;
}
