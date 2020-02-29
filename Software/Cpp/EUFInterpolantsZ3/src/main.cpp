#include <iostream>
// #include <fstream>
// #include <cstdlib>
// #include <ctime>

#include <algorithm>
#include "Rename.h"
#include "EUFInterpolant.h"
#include "UnionFindExplain.h"

void test1();
void test2();

int main(int argc, char ** argv){
 
  // z3::context ctx;
  // z3::sort my_sort = ctx.uninterpreted_sort("A");
  // z3::expr z1 = ctx.constant("z1", my_sort);
  // z3::expr z2 = ctx.constant("z2", my_sort);
  // z3::expr y1 = ctx.constant("y1", my_sort);
  // z3::expr y2 = ctx.constant("y2", my_sort);
  // z3::expr s1 = ctx.constant("s1", my_sort);
  // z3::expr s2 = ctx.constant("s2", my_sort);
  // z3::expr v = ctx.constant("v", my_sort);
  // z3::expr t = ctx.constant("t", my_sort);
  // z3::func_decl f = ctx.function("f", my_sort, my_sort, my_sort);
  // z3::func_decl g = ctx.function("g", my_sort, my_sort);
  // std::set<std::string> uncomms;
  // uncomms.insert("v");
  
  // // z3::expr alpha = f(z1, v) == s1 && f(z2, v) == s2 && f(f(y1, v), f(y2, v)) == t && s1 != t;
  // z3::expr alpha = f(z1, v) == s1 && f(z2, v) == s2 && f(f(y1, v), f(y2, v)) == t && s1 != t && g(g(s1)) == s2 && g(g(f(y1, v))) == f(y2, v);
  // z3::expr r_alpha = rename(alpha, uncomms);
  
  // EUFInterpolant euf(r_alpha);
  // // std::cout << euf << std::endl;
    
  // // euf.buildInterpolant();

  UnionFindExplain a(10);
  a.merge(1, 0);
  a.merge(0, 2);
  a.merge(4, 3);
  a.merge(4, 5);
  a.merge(2, 6);
  a.merge(5, 2);

  std::cout << "Explaining 6, 5" << std::endl;
  for(auto x : a.explain(6, 5))
    std::cout << x << std::endl;

  std::cout << "Explaining 5, 6" << std::endl;
  for(auto x : a.explain(5, 6))
    std::cout << x << std::endl;

  std::cout << "Explaining 1, 6" << std::endl;
  for(auto x : a.explain(1, 6))
    std::cout << x << std::endl;

  std::cout << "Explaining 6, 1" << std::endl;
  for(auto x : a.explain(6, 1))
    std::cout << x << std::endl;
  
  return 0;
}

void test1(){
  z3::context ctx;
  z3::expr input = mk_and(ctx.parse_file("/home/jose/Downloads/QF_UF/2018-Goel-hwbench/QF_UF_needham.3.prop4_ab_cti_max.smt2"));
  EUFInterpolant euf(input);
  std::cout << euf << std::endl;
}

void test2(){
  z3::context ctx;
  z3::sort my_sort = ctx.uninterpreted_sort("A");
  z3::expr a = ctx.constant("a", my_sort);
  z3::expr b = ctx.constant("b", my_sort);
  z3::expr c = ctx.constant("c", my_sort);
  z3::expr d = ctx.constant("d", my_sort);
  z3::func_decl f = ctx.function("f", my_sort, my_sort);
  z3::expr input = a == b && f(a) == c && f(b) == d;
  EUFInterpolant euf(input);
  std::cout << euf << std::endl;
}
