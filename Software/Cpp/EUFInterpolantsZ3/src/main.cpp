#include <iostream>
// #include <fstream>
// #include <cstdlib>
// #include <ctime>
// #include "EUFInterpolant.h"
#include <z3++.h>

int main(int argc, char ** argv){
  
  z3::context ctx;  
  z3::sort my_sort = ctx.uninterpreted_sort("A");
  z3::expr z1 = ctx.constant("z1", my_sort);
  z3::expr z2 = ctx.constant("z2", my_sort);
  z3::expr y1 = ctx.constant("y1", my_sort);
  z3::expr y2 = ctx.constant("y2", my_sort);
  z3::expr s1 = ctx.constant("s1", my_sort);
  z3::expr s2 = ctx.constant("s2", my_sort);
  z3::expr v = ctx.constant("v", my_sort);
  z3::expr t = ctx.constant("t", my_sort);
  z3::func_decl f = ctx.function("f", my_sort, my_sort, my_sort);
  
  z3::expr alpha = f(z1, v) == s1 && f(z2, v) == s2 && f(f(y1, v), f(y2, v)) == t;

  std::cout << alpha << std::endl;
      
  // EUFInterpolant euf(input_formula, symbols_to_elim, aux_expr.decl().range());
  // auto result = euf.buildInterpolant();
      

  return 0;
}
