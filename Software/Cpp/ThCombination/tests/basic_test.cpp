#include "ThCombInterpolatorWithExpressions.h"

void notAnOctagonNotATest(z3::context &);
void combinedOctagonTest(z3::context &);
void actualTest(z3::context &);
void itSatsNotATest(z3::context &);
void actualExample(z3::context &);
void exampleFromCombinedCovers1(z3::context &);
void range2InequalityExample(z3::context &);
void range3InequalityExample(z3::context &);
void range4InequalityExample(z3::context &);
void range5InequalityExample(z3::context &);
void range6InequalityExample(z3::context &);

int main(){
  
  z3::context ctx;  

  //notAnOctagonNotATest(ctx);
  combinedOctagonTest(ctx);
  //actualTest(ctx);
  //itSatsNotATest(ctx);
  //actualExample(ctx);
  
  // This one doesn't work 
  // because it contains an inequality
  // which is not an octagon inequality
  //exampleFromCombinedCovers1(ctx); 
  
  //range2InequalityExample(ctx);
  //range3InequalityExample(ctx);
  //range4InequalityExample(ctx);

  return 0;
}

void notAnOctagonNotATest(z3::context & ctx){
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
  formula_b.push_back(x3 + 1 <= y3);
  try { 
    ThCombInterpolatorWithExpressions test(formula_a, formula_b);
  }
  catch(char * const e){
    std::cout << e << std::endl;
  }
  //std::cout << test << std::endl;
}

void combinedOctagonTest(z3::context & ctx){
  z3::sort int_sort =  ctx.int_sort();

  z3::expr x1 = ctx.constant("x1", int_sort);
  z3::expr x2 = ctx.constant("x2", int_sort);
  z3::expr y1 = ctx.constant("y1", int_sort);
  z3::expr y3 = ctx.constant("y3", int_sort);
  z3::expr a  = ctx.constant("a", int_sort);
  z3::expr b  = ctx.constant("b", int_sort);

  z3::func_decl f = ctx.function("f", int_sort, int_sort);
  z3::func_decl g = ctx.function("g", int_sort, int_sort);

  z3::expr_vector formula_a(ctx); 
  formula_a.push_back(f(x1) + x2 == 0);
  formula_a.push_back(y3 == f(y1));
  formula_a.push_back(y1 <= x1);

  z3::expr_vector formula_b(ctx); 
  formula_b.push_back(x2 == g(b));
  formula_b.push_back(0 == g(b));
  formula_b.push_back(x1 <= y1);
  formula_b.push_back(1 <= y3);
  try { 
    ThCombInterpolatorWithExpressions test(formula_a, formula_b);
  }
  catch(char * const e){
    std::cout << e << std::endl;
  }
  //std::cout << test << std::endl;
}

void actualTest(z3::context & ctx){
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
  std::cout << test << std::endl;
}

void itSatsNotATest(z3::context & ctx){
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
  std::cout << test << std::endl;
}

void exampleFromCombinedCovers1(z3::context & ctx){
  z3::sort int_sort = ctx.int_sort();
  z3::expr e1 = ctx.constant("e1", int_sort);
  z3::expr x1 = ctx.constant("x1", int_sort);
  z3::expr e2 = ctx.constant("e2", int_sort);
  z3::expr x2 = ctx.constant("x2", int_sort);
  z3::expr e3 = ctx.constant("e3", int_sort);
  z3::expr x3 = ctx.constant("x3", int_sort);
  z3::expr e4 = ctx.constant("e4", int_sort);
  z3::expr x4 = ctx.constant("x4", int_sort);
  z3::func_decl f = ctx.function("f", int_sort, int_sort);

  z3::expr_vector formula_a(ctx);
  formula_a.push_back(e1 == f(x1));
  formula_a.push_back(e2 == f(x2));
  formula_a.push_back(e3 == f(e3));
  formula_a.push_back(x1 == f(e4));
  formula_a.push_back((x1 + e1) <= e3); // This might fail
  formula_a.push_back(e3 <= (x2 + e2));
  formula_a.push_back(e4 == (x2 + e3));

  z3::expr_vector formula_b(ctx);
  formula_b.push_back(x2 == 0);
  formula_b.push_back(f(x1) != x1);
  formula_b.push_back(x1 > 0);
  formula_b.push_back(x1 > f(0));

  ThCombInterpolatorWithExpressions test(formula_a, formula_b);
  std::cout << test << std::endl;
}

void actualExample(z3::context & ctx){
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
  formula_a.push_back(f(x1) == 0);
  formula_a.push_back(x1 == a);
  formula_a.push_back(y1 <= a);

  z3::expr_vector formula_b(ctx); 
  formula_b.push_back(x1 <= b);
  formula_b.push_back(y1 == b);
  formula_b.push_back(f(y1) != 0);
  
  ThCombInterpolatorWithExpressions test(formula_a, formula_b);
  std::cout << test << std::endl;
}

void range2InequalityExample(z3::context & ctx){
  z3::sort int_sort =  ctx.int_sort();
  z3::expr x = ctx.constant("x", int_sort);
  z3::func_decl f = ctx.function("f", int_sort, int_sort);

  z3::expr_vector formula_a(ctx);
  formula_a.push_back(1 <= x);
  formula_a.push_back(x <= 2);
  //formula_a.push_back(f(x) == 3);

  z3::expr_vector formula_b(ctx);
  formula_b.push_back(f(x) == 3);
  formula_b.push_back(f(1) != 3);
  formula_b.push_back(f(2) != 3);

  ThCombInterpolatorWithExpressions test(formula_a, formula_b);
  std::cout << test << std::endl;
}

void range3InequalityExample(z3::context & ctx){
  z3::sort int_sort =  ctx.int_sort();
  z3::expr x = ctx.constant("x", int_sort);
  z3::func_decl f = ctx.function("f", int_sort, int_sort);

  z3::expr_vector formula_a(ctx);
  formula_a.push_back(1 <= x);
  formula_a.push_back(x <= 3);
  //formula_a.push_back(f(x) == 3);

  z3::expr_vector formula_b(ctx);
  formula_b.push_back(f(x) == 3);
  formula_b.push_back(f(1) != 3);
  formula_b.push_back(f(2) != 3);
  formula_b.push_back(f(3) != 3);

  ThCombInterpolatorWithExpressions test(formula_a, formula_b);
  std::cout << test << std::endl;
}

void range4InequalityExample(z3::context & ctx){
  z3::sort int_sort =  ctx.int_sort();
  z3::expr x = ctx.constant("x", int_sort);
  z3::func_decl f = ctx.function("f", int_sort, int_sort);

  z3::expr_vector formula_a(ctx);
  formula_a.push_back(1 <= x);
  formula_a.push_back(x <= 4);
  //formula_a.push_back(f(x) == 3);

  z3::expr_vector formula_b(ctx);
  formula_b.push_back(f(x) == 3);
  formula_b.push_back(f(1) != 3);
  formula_b.push_back(f(2) != 3);
  formula_b.push_back(f(3) != 3);
  formula_b.push_back(f(4) != 3);

  ThCombInterpolatorWithExpressions test(formula_a, formula_b);
  std::cout << test << std::endl;
}

