#include "ThCombInterpolator.h"
#include "Rename.h"
#include <string>
#define _DEBUG_ true

int main(){
  
  z3::set_param("proof", true);
  z3::set_param("pp.min_alias_size", 10000000);
  z3::context ctx;
  
  z3::sort int_sort = ctx.int_sort();
  z3::sort bool_sort = ctx.bool_sort();

  z3::expr x  = ctx.constant("x", int_sort);
  z3::expr x1 = ctx.constant("x1", int_sort);
  z3::expr x2 = ctx.constant("x2", int_sort);
  z3::expr x3 = ctx.constant("x3", int_sort);
  z3::expr y1 = ctx.constant("y1", int_sort);
  z3::expr y2 = ctx.constant("y2", int_sort);
  z3::expr y3 = ctx.constant("y3", int_sort);
  
  z3::expr a = ctx.constant("a", int_sort);
  z3::expr b = ctx.constant("b", int_sort);
  
  z3::func_decl f = ctx.function("f", int_sort, int_sort);

  // z3::expr formula_a = f(x1) + x2 == x3 && y3 == f(y1) + y2 && y1 <= x1;
  // z3::expr formula_b = x2 == g(b) && y2 == g(b) && x1 <= y1 && x3 < y3;

  z3::expr formula_a = 1 <= x && a == 1 && f(x) == 3 && f(a) == 4;
  z3::expr formula_b = x <= 2 && b == 2 && f(b) == 5;
  z3::expr formula_c = f(x) == f(a) || not(f(x) == f(b));

  z3::solver s(ctx, "QF_UFLIA");
  s.add(formula_a);
  s.add(formula_b);

  std::cout << s.to_smt2() << std::endl;

  // std::cout << formula_a.is_common() << std::endl;
  // std::cout << formula_b.is_common() << std::endl;
  // std::cout << formula_c.is_common() << std::endl;
  
  // ThCombInterpolator test = ThCombInterpolator(ctx, formula_a, formula_b);
  // std::cout << test << std::endl;

  Rename r = Rename(formula_a, formula_b);
  
  return 0;
}
