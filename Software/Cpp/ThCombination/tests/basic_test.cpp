#include "ThCombInterpolatorWithExpressions.h"

void test1(z3::context & ctx){
  z3::sort int_sort =  ctx.int_sort();

  z3::expr x1 = ctx.constant("x1", int_sort);
  z3::expr x2 = ctx.constant("x2", int_sort);
  z3::expr x3 = ctx.constant("x3", int_sort);
  z3::expr y1 = ctx.constant("y1", int_sort);
  z3::expr y2 = ctx.constant("y2", int_sort);
  z3::expr y3 = ctx.constant("y3", int_sort);
  z3::expr a  = ctx.constant("a", int_sort);
  z3::expr b  = ctx.constant("b", int_sort);

  z3::func_decl f = ctx.function("f", int_sort, int_sort);
  z3::func_decl g = ctx.function("g", int_sort, int_sort);

  z3::expr_vector formula_a(ctx); 
  formula_a.push_back(f(x1) + x2 == x3);
  formula_a.push_back(y3 == f(y1) + y2);
  formula_a.push_back(y1 <= x1);

  z3::expr_vector formula_b(ctx); 
  formula_b.push_back(x2 == g(b));
  formula_b.push_back(y2 == g(b));
  formula_b.push_back(x1 <= y1);
  formula_b.push_back(x3 < y3);
  
  ThCombInterpolatorWithExpressions test(formula_a, formula_b);
}

void test2(z3::context & ctx){
  z3::sort int_sort =  ctx.int_sort();
  z3::expr x = ctx.constant("x", int_sort);
  z3::func_decl f = ctx.function("f", int_sort, int_sort);

  z3::expr_vector formula_a(ctx);
  formula_a.push_back(1 <= x);
  formula_a.push_back(f(x) == 3);
  formula_a.push_back(f(1) != 3);

  z3::expr_vector formula_b(ctx);
  formula_b.push_back(x <= 2);
  formula_a.push_back(f(2) != 3);

  ThCombInterpolatorWithExpressions test(formula_a, formula_b);
}

void test3(z3::context & ctx){
  z3::sort int_sort =  ctx.int_sort();
  z3::expr x = ctx.constant("x", int_sort);
  z3::func_decl f = ctx.function("f", int_sort, int_sort);

  z3::expr_vector formula_a(ctx);
  formula_a.push_back(1 <= x);
  formula_a.push_back(f(x) == 3);
  formula_a.push_back(f(1) != 3);

  z3::expr_vector formula_b(ctx);
  formula_b.push_back(x <= 2);
  formula_a.push_back(f(2) != 2);

  ThCombInterpolatorWithExpressions test(formula_a, formula_b);
}

int main(){
  
  z3::context ctx;  

  test1(ctx);
  //test2(ctx);
  //test3(ctx);

  return 0;
}
