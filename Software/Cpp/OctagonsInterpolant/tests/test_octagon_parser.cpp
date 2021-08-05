#include "OctagonInterpolantWithUncomSymbols.h"

int main(){

  z3::context ctx;
  z3::expr x1 = ctx.int_const("x1");
  z3::expr x2 = ctx.int_const("x2");
  z3::expr x3 = ctx.int_const("x3");
  z3::expr x4 = ctx.int_const("x4");
  z3::expr x5 = ctx.int_const("x5");
  z3::expr x6 = ctx.int_const("x6");

  z3::expr_vector assertions(ctx);
  assertions.push_back(x1 - x2 <= -4);
  assertions.push_back(-x2 - x3 <= 5);
  assertions.push_back(x2 + x6 <=  4);
  assertions.push_back(x2 + x5 <= -3);

  try {
    OctagonInterpolantWithUncomSymbols _a(assertions, {"x2"});
    std::cout << _a.removePrefix(_a.getInterpolant()) << std::endl;
  }
  catch(char const * e){
    std::cout << e << std::endl;
  }

  return 0;
}
