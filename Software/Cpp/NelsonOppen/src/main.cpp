#include "Purifier.h"
#include "UtilsProof.h"
#include <vector>

int main(){
  
  z3::set_param("proof", "true");
  z3::context c;
  
  z3::sort _s = c.int_sort();
  z3::expr x1 = c.constant("x1", _s);
  z3::expr x2 = c.constant("x2", _s);
  z3::expr x3 = c.constant("x3", _s);
  z3::func_decl g = c.function("g", _s, _s);
  
  z3::func_decl f = c.function("f", _s, _s);
  z3::expr formula = f(f(x1) - f(x2)) != f(x3) && x1 <= x2 && (x2 + x3) <= x1 && 0 <= x3 && f(x1) <= f(x2);
  // z3::expr formula = x1 <= f(x1);
  // z3::expr formula = (x2 >= x1) && ((x1 - x3) >= x2) && (x3 >= 0)
  //    && (f(f(x1) - f(x2)) != f(x3));
  // z3::expr formula = g(f(x1 - 2)) == x1 + 2 && g(f(x2)) == x2 - 2 && (x2 + 1 == x1 - 1);
  
  // z3::func_decl f = c.function("f", _s, _s, _s);
  // z3::expr formula =
  //   f(x1, 0) >= x3
  //   && f(x2, 0) <= x3
  //   && x1 >= x2
  //   && x2 >= x1
  //   && (x3 - f(x1, 0) >= 1);
  
  // std::cout << "Original input formula:" << std::endl;
  // std::cout << formula << std::endl;

  Purifier p = Purifier(formula);
  std::cout << p << std::endl;

  z3::solver s(c);
  addConjunction(s, formula);

  switch(s.check()){
  case z3::sat:
    std::cout << "Sat" << std::endl;
    break; 
  case z3::unsat:{
    std::cout << "Unsat" << std::endl;
    
    z3::expr_vector consequents = collectEqualitiesFromProof(s.proof());

    std::cout << std::endl;
    std::cout << "Terms collected:" <<  std::endl;
    auto num = consequents.size();
    for(unsigned i = 0; i < num; i++)
      std::cout << i << ". " << consequents[i].arg(0) << " = " << consequents[i].arg(1) << std::endl;
    
    break;
  }
  case z3::unknown:
    std::cout << "Unknown" << std::endl;
    break; 
  }
    
  return 0;
}
