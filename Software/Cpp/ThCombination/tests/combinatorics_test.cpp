#include "Combinatorics.h"

int main(){
  z3::context ctx;
  z3::sort int_sort = ctx.int_sort();
  z3::expr x1 = ctx.constant("x1", int_sort);
  z3::expr x2 = ctx.constant("x2", int_sort);
  z3::expr x3 = ctx.constant("x3", int_sort);
  z3::expr x4 = ctx.constant("x4", int_sort);
  z3::expr x5 = ctx.constant("x5", int_sort);
  z3::expr x6 = ctx.constant("x6", int_sort);
  z3::expr x7 = ctx.constant("x7", int_sort);
  std::vector<z3::expr> elems({});
  elems.push_back(x1);
  elems.push_back(x2);
  elems.push_back(x3);
  elems.push_back(x4);
  elems.push_back(x5);
  elems.push_back(x6);
  elems.push_back(x7);

  Combinatorics c(elems);
  auto res = c.makeCombinations(4);
  for(auto const & y : res){
    for(auto const & x : y)
      std::cout << x << " ";
    std::cout << std::endl;
  }

  return 0;
}
