#include "Purifier.h"

int main(){
  
  z3::context c;
  
  z3::sort Q = c.real_sort();
  z3::expr x1 = c.constant("x1", Q);
  z3::expr x2 = c.constant("x2", Q);
  z3::expr x3 = c.constant("x3", Q);
  
  z3::func_decl f = c.function("f", Q, Q);
  z3::expr formula = f(f(x1) - f(x2)) != f(x3) && x1 <= x2 && (x2 + x3) <= x1 && 0 <= x3 && f(x1) <= f(x2);
  // z3::expr formula = f(f(x1) - f(x2)) != f(x3) && x1 <= x2 && (x2 + x3) <= x1 && 0 <= x3;
  // z3::expr formula = x1 <= f(x1);
  // z3::expr formula = (x2 >= x1) && ((x1 - x3) >= x2) && (x3 >= 0)
  //    && (f(f(x1) - f(x2)) != f(x3));

  // z3::func_decl g = c.function("g", Q, Q);
  // z3::expr formula = g(f(x1 - 2)) == x1 + 2 && g(f(x2)) == x2 - 2 && (x2 + 1 == x1 - 1);
  
  // z3::func_decl f = c.function("f", Q, Q, Q);
  // z3::expr formula =
  //   f(x1, 0) >= x3
  //   && f(x2, 0) <= x3
  //   && x1 >= x2
  //   && x2 >= x1
  //   && (x3 - f(x1, 0) >= 1);
  
  std::cout << "Original: " << formula << std::endl;

  Purifier p = Purifier(formula);
  std::cout << p << std::endl;
  
  return 0;
}
