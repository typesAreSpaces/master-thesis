#include "OctagonInterpolantWithUncomSymbols.h"

int main(){

  z3::context ctx;
  z3::expr x1 = ctx.int_const("w1");
  z3::expr x2 = ctx.int_const("w2");
  z3::expr x3 = ctx.int_const("w3");
  z3::expr x4 = ctx.int_const("w4");

  z3::expr_vector assertions(ctx);
  assertions.push_back(x1 + x2  <= -121);
  assertions.push_back(-x1 + x3 <= 19);
  assertions.push_back(x2 - x1  <= 51);
  assertions.push_back(- x3  <= 51);
  assertions.push_back(x3  <= -51);
  assertions.push_back(x4  <= 0);
  assertions.push_back(x2 + (-x1)  <= 501);

  try {
    OctagonInterpolantWithUncomSymbols _a(assertions, {"w1", "w2", "w3", "w4"});
    std::cout << _a.removePrefix(_a.getInterpolant()) << std::endl;
  }
  catch(char const * e){
    std::cout << e << std::endl;
  }

  return 0;
}
