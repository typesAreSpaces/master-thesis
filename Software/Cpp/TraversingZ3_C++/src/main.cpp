/*++
  Copyright (c) 2015 Microsoft Corporation

  --*/

#include "z3++.h"
#include "util.h"
#include "traversal.h"
#include <set>
/*
void tst_visit() {
    std::cout << "visit example\n";
    z3::context c;

    z3::expr x = c.int_const("x");
    z3::expr y = c.int_const("y");
    z3::expr f = x*y - y*x >= 0;
    z3::expr f2 = f && f;
    
    visit(f2);
}

void tst_visit2() {
    std::cout << "visit example\n";
    z3::context c;

    z3::expr x = c.int_const("x");
    z3::expr y = c.int_const("y");
    z3::expr f = x*y - y*x >= 0;
    z3::expr f2 = f && f;

    visitPostOrderWithStack(f2);
}
*/
int main(int argc, char ** argv) {
  
  //std::string file = "./SMT2_files/interpolantExample1.smt2";
  std::string file = argv[1];
  
  z3::config cfg;
  cfg.set("PROOF", true);
  cfg.set("MODEL", true);
  cfg.set("TRACE", false);
  z3::context ctx(cfg);

  z3::expr inputFormula = ctx.parse_file(file.c_str());
  
  visit(inputFormula);
  //visitPostOrderWithStack(inputFormula);
  
  return 0;
}
