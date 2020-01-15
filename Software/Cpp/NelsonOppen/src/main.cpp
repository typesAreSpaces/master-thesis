#include "ThCombInterpolator.h"
#define _DEBUG_ true

int main(){
  
  z3::set_param("proof", true);
  z3::set_param("pp.single_line", true);
  z3::context ctx;
  
  z3::sort int_sort = ctx.int_sort();
  z3::expr x1 = ctx.constant("x1", int_sort);
  z3::expr x2 = ctx.constant("x2", int_sort);
  z3::expr x3 = ctx.constant("x3", int_sort);
  z3::func_decl g = ctx.function("g", int_sort, int_sort);
 
  z3::func_decl f1 = ctx.function("f", int_sort, int_sort);
  z3::expr formula1 = x1 <= f1(x1);
  z3::expr formula2 = x2 >= x1 && (x1 - x3) >= x2 && x3 >= 0 && f1(f1(x1) - f1(x2)) != f1(x3);
  z3::expr formula3 = g(f1(x1 - 2)) == x1 + 2 && g(f1(x2)) == x2 - 2 && (x2 + 1 == x1 - 1);
  
  z3::func_decl f2 = ctx.function("f", int_sort, int_sort, int_sort);
  z3::expr formula4 = f2(x1, 0) >= x3
    && f2(x2, 0) <= x3
    && x1 >= x2
    && x2 >= x1
    && (x3 - f2(x1, 0) >= 1);
 
  z3::expr & formula_current_test = formula4;
  
  ThCombInterpolator p = ThCombInterpolator(formula_current_test);

  p.collectEqualities();
  std::cout << p << std::endl;
  
  return 0;
}
