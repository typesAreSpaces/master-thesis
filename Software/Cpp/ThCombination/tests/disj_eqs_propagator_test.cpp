#include "DisjEqsPropagator.h"

void subsetSizeEnumeration(z3::expr_vector const & elems, unsigned subset_size){
  DisjEqsPropagator c(elems);
  c.subsetSetup(subset_size);
  unsigned count = 0;
  do {
    std::cout << c.getCurrentDisjEqs() << std::endl;
    ++count;
  } while(c.hasNext());
  std::cout << "Number of elements counted " << count << std::endl;
}

void allSubsetsEnumeration(z3::expr_vector const & elems){
  DisjEqsPropagator c(elems);
  auto it = c.begin();
  unsigned count = 0;
  for(; !it.isLast(); ++it){
    auto res = *it;
    //std::cout << res << std::endl;
    ++count;
  }
  std::cout << "Number of elements counted " << count << std::endl;
}

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
  z3::expr x8 = ctx.constant("x8", int_sort);

  z3::expr_vector elems(ctx);
  elems.push_back(x1);
  elems.push_back(x2);
  elems.push_back(x3);
  elems.push_back(x4);
  elems.push_back(x5);
  elems.push_back(x6);
  elems.push_back(x7);
  elems.push_back(x8);

  //subsetSizeEnumeration(elems, 3);
  allSubsetsEnumeration(elems);

  return 0;
}
