#include <iostream>
#include <algorithm>
#include "Rename.h"
#include "EUFInterpolant.h"

void currentProgress(){
 
  z3::context ctx;
  z3::sort my_sort = ctx.uninterpreted_sort("A");
  z3::expr a = ctx.constant("a", my_sort);
  z3::expr b = ctx.constant("b", my_sort);
  z3::expr c = ctx.constant("c", my_sort);
  z3::expr d = ctx.constant("d", my_sort);
  z3::expr e = ctx.constant("e", my_sort);
  z3::expr g = ctx.constant("g", my_sort);
  z3::expr h = ctx.constant("h", my_sort);
  z3::func_decl f = ctx.function("f", my_sort, my_sort, my_sort);
  z3::expr input = f(g, h) == d && c == d && f(g, d) == a && e == c && e == b && b == h;

  EUFInterpolant test(input);

  return;
}

int main(int argc, char ** argv){

  currentProgress();

  return 0;
}


