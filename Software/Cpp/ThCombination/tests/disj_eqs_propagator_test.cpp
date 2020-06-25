#include "DisjEqsPropagator.h"

void test1(std::vector<z3::expr> const & elems){
  DisjEqsPropagator c(elems);
  auto res = c.makeCombinations(11);
  unsigned count = 0;
  for(auto const & y : res){
    for(auto const & x : y)
      std::cout << x << " ";
    std::cout << std::endl;
    count++;
  }
  std::cout << count << std::endl;
}

void test2(std::vector<z3::expr> const & elems){
  DisjEqsPropagator c(elems);
  c.init(15);
  unsigned count = 0;
  while(c.next()){
    for(auto const & x : c.getCurrentCombination())
      std::cout << x << " ";
    std::cout << std::endl;
    ++count;
  }
  std::cout << count << std::endl;
}

void test3(std::vector<z3::expr> const & elems){
  DisjEqsPropagator c(elems);
  auto it = c.begin();
  unsigned i = 0;
  for(; !it.isLast(); it.next()){
    auto res = *it;
    //for(auto const & elemens : res)
      //std::cout << elemens << " ";
    //std::cout << std::endl;
    ++i;
  }
  std::cout << "Number of elements counted " << i << std::endl;
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
  std::vector<z3::expr> elems({});
  elems.push_back(x1);
  elems.push_back(x2);
  elems.push_back(x3);
  elems.push_back(x4);
  elems.push_back(x5);
  elems.push_back(x6);
  elems.push_back(x7);

  std::vector<z3::expr> elems2({});
  elems2.push_back(x1);
  elems2.push_back(x2);
  elems2.push_back(x3);
  elems2.push_back(x4);
  elems2.push_back(x5);
  elems2.push_back(x6);
  elems2.push_back(x7);
  // Currently DisjEqsPropagator cannot handle 
  // more than 7 shared variables
  elems2.push_back(x8); 
  
  //test1(elems);
  //test2(elems2);
  test3(elems2);


  return 0;
}
