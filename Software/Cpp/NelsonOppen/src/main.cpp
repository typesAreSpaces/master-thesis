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
  
  return 0;
}
