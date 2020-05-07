#include <iostream>
#include <algorithm>
#include "Rename.h"
#include "EUFInterpolant.h"

void currentProgress(){
 
  z3::context ctx;
  z3::sort my_sort = ctx.uninterpreted_sort("A");
  z3::expr a = ctx.constant("a", my_sort);
  z3::expr b = ctx.constant("b", my_sort);
  z3::func_decl g = ctx.function("g", my_sort, my_sort, my_sort, my_sort);
  z3::func_decl h = ctx.function("h", my_sort, my_sort);
  z3::expr input = g(a, h(b), b) == b && g(a, h(b), h(b)) == h(b) && g(a, h(b), h(h(b))) == h(h(b)) && h(b) == b;
  
  try {
    EUFInterpolant test(input);
    std::cout << test << std::endl;
  }
  catch(char const * e){
    std::cout << e << std::endl;
  }

  return;
}

int main(int argc, char ** argv){

  currentProgress();

  return 0;
}


