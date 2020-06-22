#include <iostream>
#include <z3++.h>
#include "CDCL_T.h"

void z3_map_example(z3::context & ctx){
  z3::sort int_sort = ctx.int_sort();

  z3::expr x1 = ctx.constant("x1", int_sort);
  z3::expr x2 = ctx.constant("x2", int_sort);
  z3::expr x3 = ctx.constant("x3", int_sort);

  z3::expr_map a(ctx);
  a.insert(x1, x2);
  a.insert(x2, x3);

  std::cout << a << std::endl;
  std::cout << a.find(x1) << std::endl;
  std::cout << a.find(x2) << std::endl;
  try {
    std::cout << a.find(x3) << std::endl;
  }
  catch(z3::exception const & e){
    std::cout << e << std::endl;
  }

  std::cout << a.contains(x1) << std::endl;
  std::cout << a.contains(x2) << std::endl;
  std::cout << a.contains(x3) << std::endl;
}

int main(){

  z3::context ctx;
  z3::sort int_sort = ctx.int_sort();
  z3::sort bool_sort= ctx.bool_sort();

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
  z3::func_decl p = ctx.function("p", int_sort, bool_sort);

  z3::expr_vector formula_a(ctx); 
  formula_a.push_back(f(x1) + x2 == x3);
  formula_a.push_back(y3 == f(y1) + y2);
  formula_a.push_back(x2 == g(b));
  formula_a.push_back(y2 == g(a));

  z3::expr_vector example_3(ctx);
  example_3.push_back(1 == x1 || 2 == x1);
  example_3.push_back(p(x1));
  example_3.push_back(not(p(1)));
  example_3.push_back(not(p(2)));

  //CDCL_T whatever(ctx, formula_a);
  CDCL_T whatever(ctx, example_3);

  return 0;
}
