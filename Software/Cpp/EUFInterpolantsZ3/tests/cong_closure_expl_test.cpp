#include <iostream>
#include "TestCongruenceClosureExplain.h"

void inputFile(char const * file_name){
  z3::context ctx;
  auto assertions = ctx.parse_file(file_name);
  std::string input_file = file_name;
  TestCongruenceClosureExplain test(assertions);
  try{
    std::cout << test.testConsistency(assertions, 20) << std::endl;
    //test.testExplanation(1);
  }
  catch(char const * e){
    std::cout << e << std::endl;
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

  z3::expr_vector input(ctx);
  input.push_back(a == b);
  input.push_back(f(a) == c);
  input.push_back(f(b) == d);

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

  z3::expr_vector input(ctx);
  input.push_back(g(a, h(b), b) == b );
  input.push_back(g(a, h(b), h(b)) == h(b) );
  input.push_back(g(a, h(b), h(h(b))) == h(h(b)));

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

  z3::expr_vector input(ctx);
  input.push_back(g(a, h(b), b) == b );
  input.push_back(g(a, h(b), h(b)) == h(b) );
  input.push_back(g(a, h(b), h(h(b))) == h(h(b)) );
  input.push_back(h(b) == b);

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

  z3::expr_vector input(ctx);
  input.push_back(g(a, h(b), b) == g(b, h(b), h(b)) );
  input.push_back(h(b) == b );
  input.push_back(a == b);

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

  z3::expr_vector input(ctx);
  input.push_back(f(g, h) == d );
  input.push_back(c == d );
  input.push_back(f(g, d) == a );
  input.push_back(e == c );
  input.push_back(e == b );
  input.push_back(b == h);
 
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
  
  testCongClosureExpl();
  testCongClosureExpl2();
  testCongClosureExpl3();
  testCongClosureExpl4();
  testCongClosureExpl5();
  
  try {
    inputFile("/home/jose/Documents/GithubProjects/master-thesis/Software/Cpp/EUFInterpolantsZ3/tests/QF_UF/SEQ/SEQ013_size6.smt2");
    inputFile("/home/jose/Documents/GithubProjects/master-thesis/Software/Cpp/EUFInterpolantsZ3/tests/QF_UF/2018-Goel-hwbench/QF_UF_v_Unidec_ab_cti_max.smt2");
  }
  catch(char const * e){
    std::cout << e << std::endl;
  }

  
 
  return 0;
}


