/*++
  Copyright (c) 2015 Microsoft Corporation

  --*/

#include "z3++.h"
#include "z3.h" 
#include "util.h"
#include "traversal.h"
#include "constructors.h"

int main(int argc, char ** argv) {
  
  //std::string file = "./SMT2_files/interpolantExample1.smt2";
  std::string file = "/Users/joseabelcastellanosjoo/Documents/QF_UF/2018-Goel-hwbench/QF_UF_firewire_tree.1.prop1_ab_cti_max.smt2";

  z3::config cfg;
  cfg.set("PROOF", true);
  cfg.set("MODEL", true);
  cfg.set("TRACE", true);
  z3::context ctx(cfg);

  Z3_ast inputFormula = Z3_parse_smtlib2_file(ctx, (Z3_string)file.c_str(), 0, 0, 0, 0, 0, 0);
  visit(ctx, stdout, inputFormula);
  
  return 0;
}
