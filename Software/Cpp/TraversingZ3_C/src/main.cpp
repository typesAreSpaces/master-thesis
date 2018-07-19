/*++
  Copyright (c) 2015 Microsoft Corporation

  --*/

#include "z3++.h"
#include "z3.h" 
#include "util.h"
#include "traversal.h"
#include "constructors.h"

void tst_display_ast() {
  z3::context c;
  Z3_ast x, y, z, f;
  x = mk_int_var(c, "x");
  y = mk_int_var(c, "y");
  z = mk_int_var(c, "z");
  f = x;
  display_ast(c, stdout, f);
}

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
 
  //tst_display_ast();
  //std::cout << std::endl;
  display_ast(ctx, stdout, inputFormula);
  std::cout << std::endl;
  return 0;
}
