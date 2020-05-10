#include <iostream>
#include "TestCongruenceClosureExplain.h"

void inputFile(char const * file_name){
  z3::context ctx;
  auto input = mk_and(ctx.parse_file(file_name));
  std::string input_file = file_name;
  TestCongruenceClosureExplain test(input);
  try{
    std::cout << test.testConsistency(input, 20) << std::endl;
  }
  catch(char const * e){
    std::cout << e << std::endl;
    test.testExplanation(20);
  }
  return;
}

void testCongClosureExpl(){
  z3::context ctx;
  z3::sort my_sort = ctx.uninterpreted_sort("A");
  z3::expr a = ctx.constant("a", my_sort);
  z3::expr b = ctx.constant("b", my_sort);
  z3::expr c = ctx.constant("c", my_sort);
  z3::expr d = ctx.constant("d", my_sort);
  z3::func_decl f = ctx.function("f", my_sort, my_sort);
  z3::expr input = a == b && f(a) == c && f(b) == d;

  TestCongruenceClosureExplain test(input);
  std::cout << test << std::endl;
  std::cout << test.testConsistency(input, 20) << std::endl;
  test.testExplanation(20);
  return;
}

void testCongClosureExpl2(){
  z3::context ctx;
  z3::sort my_sort = ctx.uninterpreted_sort("A");
  z3::expr a = ctx.constant("a", my_sort);
  z3::expr b = ctx.constant("b", my_sort);
  z3::func_decl g = ctx.function("g", my_sort, my_sort, my_sort, my_sort);
  z3::func_decl h = ctx.function("h", my_sort, my_sort);
  z3::expr input = g(a, h(b), b) == b && g(a, h(b), h(b)) == h(b) && g(a, h(b), h(h(b))) == h(h(b));

  TestCongruenceClosureExplain test(input);
  std::cout << test << std::endl;
  std::cout << test.testConsistency(input, 20) << std::endl;
  test.testExplanation(20);
  return;
}

void testCongClosureExpl3(){
  z3::context ctx;
  z3::sort my_sort = ctx.uninterpreted_sort("A");
  z3::expr a = ctx.constant("a", my_sort);
  z3::expr b = ctx.constant("b", my_sort);
  z3::func_decl g = ctx.function("g", my_sort, my_sort, my_sort, my_sort);
  z3::func_decl h = ctx.function("h", my_sort, my_sort);
  z3::expr input = g(a, h(b), b) == b && g(a, h(b), h(b)) == h(b) && g(a, h(b), h(h(b))) == h(h(b)) && h(b) == b;

  TestCongruenceClosureExplain test(input);
  std::cout << test << std::endl;
  std::cout << test.testConsistency(input, 20) << std::endl;
  test.testExplanation(20);
  return;
}

void testCongClosureExpl4(){
  z3::context ctx;
  z3::sort my_sort = ctx.uninterpreted_sort("A");
  z3::expr a = ctx.constant("a", my_sort);
  z3::expr b = ctx.constant("b", my_sort);
  z3::func_decl g = ctx.function("g", my_sort, my_sort, my_sort, my_sort);
  z3::func_decl h = ctx.function("h", my_sort, my_sort);
  z3::expr input = g(a, h(b), b) == g(b, h(b), h(b)) && h(b) == b && a == b;

  TestCongruenceClosureExplain test(input);
  std::cout << test << std::endl;
  std::cout << test.testConsistency(input, 20) << std::endl;
  test.testExplanation(20);
  return;
}

void testCongClosureExpl5(){
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

  TestCongruenceClosureExplain test(input);
  std::cout << test << std::endl;
  std::cout << test.testConsistency(input, 20) << std::endl;
  test.testExplanation(20);
  return;
}

int main(int argc, char ** argv){

  // Current observation: Since the init method
  // doesn't process inequalities, we cannot 
  // reach unsat in QF_UF. Hence, we cannot 
  // check that a formula has false as representative.
  
  //testCongClosureExpl();
  //testCongClosureExpl2();
  //testCongClosureExpl3();
  //testCongClosureExpl4();
  //testCongClosureExpl5();
 
  inputFile("/home/jose/Documents/GithubProjects/master-thesis/Software/Cpp/EUFInterpolantsZ3/tests/QF_UF/2018-Goel-hwbench/QF_UF_v_Unidec_ab_cti_max.smt2");

  return 0;
}


