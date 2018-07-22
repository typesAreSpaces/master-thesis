/*++
  Copyright (c) 2015 Microsoft Corporation

  --*/

#include "z3++.h"
#include "util.h"
#include "traversal.h"

int main(int argc, char ** argv) {

  //std::string file = "/Users/joseabelcastellanosjoo/Documents/QF_UF/2018-Goel-hwbench/QF_UF_firewire_tree.5.prop3_ab_reg_max.smt2";
  //std::string file = "/Users/joseabelcastellanosjoo/Documents/QF_UF/2018-Goel-hwbench/QF_UF_firewire_tree.1.prop1_ab_cti_max.smt2";
  std::string file = "./SMT2_files/interpolantExample1.smt2";
  //std::string file = argv[1];
  
  z3::config cfg;
  cfg.set("PROOF", true);
  cfg.set("MODEL", true);
  cfg.set("TRACE", false);
  z3::context ctx(cfg);

  //z3::expr inputFormula = ctx.parse_file(file.c_str());
  //visit(inputFormula);
  //z3::goal g(ctx);
  //g.add(inputFormula);
  
  //std::cout << g.num_exprs() << std::endl;

  proveFromFile(file);
  
  return 0;
}
