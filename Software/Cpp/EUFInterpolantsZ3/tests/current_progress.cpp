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

  z3::expr_vector input(ctx); 
  input.push_back(g(a, h(b), b) == b );
  input.push_back(g(a, h(b), h(b)) == h(b) );
  input.push_back(g(a, h(b), h(h(b))) == h(h(b)) );
  input.push_back(h(b) == b);
  input.push_back(a != b);
  //input.push_back(h(h(b)) != b);

  try {
    EUFInterpolant eufi(input);
  }
  catch(char const * e){
    std::cout << e << std::endl;
  }

  return;
}

void paperExample(){

  z3::context ctx;
  z3::sort my_sort = ctx.uninterpreted_sort("A");
  z3::expr z1 = ctx.constant("z1", my_sort);
  z3::expr z2 = ctx.constant("z2", my_sort);
  z3::expr s1 = ctx.constant("s1", my_sort);
  z3::expr s2 = ctx.constant("s2", my_sort);
  z3::expr y1 = ctx.constant("y1", my_sort);
  z3::expr y2 = ctx.constant("y2", my_sort);
  z3::expr v = ctx.constant("v", my_sort);
  z3::expr t = ctx.constant("t", my_sort);
  z3::func_decl f = ctx.function("f", my_sort, my_sort, my_sort);
  std::set<std::string> uncomms;
  uncomms.insert("v");

  z3::expr alpha = f(z1, v) == s1 && f(z2, v) == s2 && f(f(y1, v), f(y2, v)) == t;
  z3::expr r_alpha = rename(alpha, uncomms);

  z3::expr_vector input(ctx); 
  input.push_back(f(z1, v) == s1);
  input.push_back(f(z2, v) == s2);
  input.push_back(f(f(y1, v), f(y2, v)) == t);

  try {
    //EUFInterpolant eufi(input); // FIX:
    auto ok = f(z1, v);
    std::cout << ok << " " << ok.is_common() << std::endl;
    auto ok2 = f(f(y1, v), f(y2, v));
    std::cout << ok2 << " " << ok2.is_common() << std::endl;
    //std::cout << alpha << std::endl;
    std::cout << r_alpha << std::endl;
  }
  catch(char const * e){
    std::cout << e << std::endl;
  }

  return;
}



int main(int argc, char ** argv){

  //currentProgress();
  paperExample();

  return 0;
}


