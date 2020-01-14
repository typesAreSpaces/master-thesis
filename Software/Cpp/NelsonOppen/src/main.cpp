#include "ThCombInterpolator.h"
#define _DEBUG_ true

int main(){
  
  z3::set_param("proof", "true");
  z3::context c;
  
  z3::sort _s = c.int_sort();
  z3::expr x1 = c.constant("x1", _s);
  z3::expr x2 = c.constant("x2", _s);
  z3::expr x3 = c.constant("x3", _s);
  z3::func_decl g = c.function("g", _s, _s);
 
  z3::func_decl f1 = c.function("f", _s, _s);
  z3::expr formula1 = x1 <= f1(x1);
  z3::expr formula2 = x2 >= x1 && (x1 - x3) >= x2 && x3 >= 0 && f1(f1(x1) - f1(x2)) != f1(x3);
  z3::expr formula3 = g(f1(x1 - 2)) == x1 + 2 && g(f1(x2)) == x2 - 2 && (x2 + 1 == x1 - 1);
  
  z3::func_decl f2 = c.function("f", _s, _s, _s);
  z3::expr formula4 = f2(x1, 0) >= x3
    && f2(x2, 0) <= x3
    && x1 >= x2
    && x2 >= x1
    && (x3 - f2(x1, 0) >= 1);
 
  z3::expr & formula_current_test = formula3;
#if _DEBUG_  
  std::cout << "Original input formula:" << std::endl;
  std::cout << formula_current_test << std::endl;
#endif
  
  ThCombInterpolator p = ThCombInterpolator(formula_current_test);
#if _DEBUG_  
  std::cout << "Formula after purification" << std::endl;
  std::cout << formula_current_test << std::endl;
#endif

  p.collectEqualities();
  std::cout << p << std::endl;

  // z3::solver ss(c, "QF_UF");
  // z3::expr a1 = c.constant("a1", f1.range());
  // z3::expr a2 = c.constant("a2", f1.range());
  // z3::expr a3 = c.constant("a3", f1.range());
  // z3::expr a4 = c.constant("a4", f1.range());
  // z3::expr a5 = c.constant("a5", f1.range());

  // ss.add(g(f1(a2)) == a1);
  // ss.add(g(f1(x2)) == a3);
  // ss.add(a5 == a4);
  // ss.add(g(f1(x2)) == a3);
  // ss.add(x2 == 2 + a3);
  // ss.add(!(f1(x2) == f1(2 + a3)));

  // std::cout << ss.assertions() << std::endl;

  // switch(ss.check()){
  // case z3::unsat:
  //   std::cout << "unsat" << std::endl;
  //   break;
  // case z3::sat:
  //   std::cout << "sat" << std::endl;
  //   break;
  // case z3::unknown:
  //   std::cout << "unknown" << std::endl;
  //   break;
  // }
  
  return 0;
}
