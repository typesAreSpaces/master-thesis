#include "OctagonInterpolantWithUncomSymbols.h"

void example1(z3::context &);
void example2(z3::context &);
void example3(z3::context &);
void example4(z3::context &);

int main(){
  z3::context ctx;

  //example1(ctx);
  //example2(ctx);
  //example3(ctx);
  example4(ctx);

  return 0;
}

void example1(z3::context & ctx){
  z3::expr x1 = ctx.int_const("x1");
  z3::expr x2 = ctx.int_const("x2");
  z3::expr x3 = ctx.int_const("x3");
  z3::expr x4 = ctx.int_const("x4");
  z3::expr x5 = ctx.int_const("x5");
  z3::expr x6 = ctx.int_const("x6");

  z3::expr_vector assertions(ctx);
  assertions.push_back(-x1 + x2 <= 4);
  assertions.push_back(x2 + x3 <= -5);
  assertions.push_back(-x2 - x6 <= -4);
  assertions.push_back(-x2 - x5 <= 3);

  try {
    OctagonInterpolantWithUncomSymbols _a(assertions, {"x2"});
    std::cout << _a.removePrefix(_a.getInterpolant()) << std::endl;
  }
  catch(char const * e){
    std::cout << e << std::endl;
  }
}

void example2(z3::context & ctx){

  z3::expr x1 = ctx.int_const("x1");
  z3::expr x2 = ctx.int_const("x2");
  z3::expr x3 = ctx.int_const("x3");
  z3::expr x4 = ctx.int_const("x4");
  z3::expr x5 = ctx.int_const("x5");
  z3::expr x6 = ctx.int_const("x6");

  z3::expr_vector assertions(ctx);
  assertions.push_back(x2 + x1 <= 3);
  assertions.push_back(-x3 - x1 <= 1);
  assertions.push_back(x4 + x3 <= -6);
  assertions.push_back(-x5 - x4 <= 1);

  try {
    OctagonInterpolantWithUncomSymbols _a(assertions, {"x1"});
    std::cout << _a.removePrefix(_a.getInterpolant()) << std::endl;
  }
  catch(char const * e){
    std::cout << e << std::endl;
  }
}

void example3(z3::context & ctx){

  z3::expr x1 = ctx.int_const("x1");
  z3::expr x2 = ctx.int_const("x2");
  z3::expr x3 = ctx.int_const("x3");
  z3::expr x4 = ctx.int_const("x4");

  z3::expr_vector assertions(ctx);
  assertions.push_back(x1 + x2 <= 1);
  assertions.push_back(x3 - x2 <= 1);
  assertions.push_back(x4 - x3 <= 1);
  assertions.push_back(x1 - x4 <= 1);

  try {
    OctagonInterpolantWithUncomSymbols _a(assertions, {"x2", "x3", "x4"});
    std::cout << _a.removePrefix(_a.getInterpolant()) << std::endl;
  }
  catch(char const * e){
    std::cout << e << std::endl;
  }
}

void example4(z3::context & ctx){

  z3::expr x1 = ctx.int_const("x1");
  z3::expr x2 = ctx.int_const("x2");
  z3::expr x3 = ctx.int_const("x3");
  z3::expr x4 = ctx.int_const("x4");
  z3::expr x5 = ctx.int_const("x5");
  z3::expr x6 = ctx.int_const("x6");

  z3::expr_vector assertions(ctx);
  assertions.push_back(x1 + x2 <= 1);
  assertions.push_back(x3 - x2 <= 1);
  assertions.push_back(x4 - x3 <= 1);
  assertions.push_back(x5 - x4 <= 1);
  assertions.push_back(x6 - x5 <= 1);
  assertions.push_back(x1 - x6 <= 1);

  try {
    OctagonInterpolantWithUncomSymbols _a(assertions, {"x2", "x3", "x4", "x5", "x6"});
    std::cout << _a.removePrefix(_a.getInterpolant()) << std::endl;
  }
  catch(char const * e){
    std::cout << e << std::endl;
  }
}
