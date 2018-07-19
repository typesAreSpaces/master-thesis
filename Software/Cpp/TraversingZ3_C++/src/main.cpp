/*++
  Copyright (c) 2015 Microsoft Corporation

  --*/

#include "z3++.h"
#include "util.h"
#include "traversal.h"

void tst_visit() {
    std::cout << "visit example\n";
    z3::context c;

    z3::expr x = c.int_const("x");
    z3::expr y = c.int_const("y");
    z3::expr z = c.int_const("z");
    z3::expr f = x*x - y*y >= 0;

    visit(f);
}

int main(int argc, char ** argv) {

  //testSMT2(argc, argv);
  //interface();
  
  std::string file = "./SMT2_files/interpolantExample1.smt2";
  z3::config cfg;
  cfg.set("PROOF", true);
  cfg.set("MODEL", true);
  cfg.set("TRACE", false);
  z3::context ctx(cfg);

  z3::expr inputFormula = ctx.parse_file(file.c_str());
  
  //tst_visit();
  visit(inputFormula);
  return 0;
}
