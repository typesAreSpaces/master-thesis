/*++
  Copyright (c) 2015 Microsoft Corporation

  --*/

#include <vector>
#include "z3++.h"
#include "util.h"

int main(int argc, char ** argv) {

  //testSMT2(argc, argv);
  //interface();

  std::string file = "./SMT2_files/interpolantExample1.smt2";
  z3::config cfg;
  cfg.set("PROOF", true);
  cfg.set("MODEL", true);
  cfg.set("TRACE", true);
  z3::context ctx(cfg);
  Z3_ast inputFormula = Z3_parse_smtlib2_file(ctx, (Z3_string)file.c_str(), 0, 0, 0, 0, 0, 0);
  z3::expr _inputFormula(ctx, inputFormula);

  std::cout << _inputFormula << std::endl;
  
  return 0;
}
