#include "Purifier.h"

int main(){
  
  z3::context c;
  z3::expr_vector from(c);
  z3::expr_vector to(c);

  z3::sort Q = c.real_sort();
  z3::expr x = c.constant("x1", Q);
  z3::expr y = c.constant("x2", Q);
  z3::expr z = c.constant("x3", Q);

  // z3::func_decl f = c.function("f", Q, Q);
  // z3::expr formula = f(f(x) - f(y)) != f(z) && x <= y && (y + z) <= x && 0 <= z && f(x) <= f(y);
  // z3::expr formula = f(f(x) - f(y)) != f(z) && x <= y && (y + z) <= x && 0 <= z;
  // z3::expr formula = x <= f(x);
  
  z3::func_decl f = c.function("f", Q, Q, Q);
  z3::expr formula =
    f(x, 0) >= z
    && f(y, 0) <= z
    && x >= y
    && y >= x
    && (z - f(x, 0) >= -1)
    && -x <= 0;
  
  std::cout << "Original: " << formula << std::endl;

  Purifier p = Purifier(formula); 
  std::cout << "Purified: " << p.purify() << std::endl;
  
  return 0;
}
