#include "OctagonParser.h"
#include <z3++.h>

int main(){


  z3::context ctx;
  z3::expr x1 = ctx.int_const("x1");
  z3::expr x2 = ctx.int_const("x2");
  z3::expr x3 = ctx.int_const("x3");

  z3::expr_vector assertions(ctx);
  assertions.push_back(x1 + x2  <= -121);
  assertions.push_back(-x1 + x3 <= 19);
  assertions.push_back(x2 - x1  <= 51);
  assertions.push_back(- x3  <= 51);
  assertions.push_back(x3  <= -51);
  assertions.push_back(x2 + (-x1)  <= 501);

  OctagonParser _p(assertions);

  return 0;
}
