#include <iostream>
#include <z3++.h>

int main(int argc, char ** argv){
  z3::set_param("proof", true);
  z3::set_param("pp.single_line", true);
  
  z3::context ctx;

  z3::solver s(ctx, "QF_UFLIA");
  // s.from_file("./tests/a.smt2");
  s.from_file("./tests/c.smt2");
  // s.from_file("./tests/QF_UFLIA/mathsat/Hash/hash_uns_03_03.smt2");
  if(s.check() == z3::unsat)
    std::cout << s.proof() << std::endl;
  return 0;
}
