#include <iostream>
#include <z3++.h>
#include "DisequalitiesFlattener.h"

int main(){

  z3::context ctx;

  z3::expr x1 = ctx.constant("x1", ctx.int_sort());
  z3::expr x2 = ctx.constant("x2", ctx.int_sort());
  z3::expr x3 = ctx.constant("x3", ctx.int_sort());
  z3::func_decl f = ctx.function("f", ctx.int_sort(), ctx.int_sort());

  z3::expr_vector assertions(ctx);
  assertions.push_back(x1 == x2);
  assertions.push_back(f(f(x1)) == x2);
  assertions.push_back(f(x2) != x3);
  assertions.push_back(f(x1) != x3);

  DisequalitiesFlattener ok(assertions);
  std::cout << ok << std::endl;

  return 0;
}
