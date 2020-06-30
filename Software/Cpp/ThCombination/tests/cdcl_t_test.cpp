#include "CDCL_T.h"

void z3_map_example(z3::context & ctx){
  z3::sort int_sort = ctx.int_sort();

  z3::expr x1 = ctx.constant("x1", int_sort);
  z3::expr x2 = ctx.constant("x2", int_sort);
  z3::expr x3 = ctx.constant("x3", int_sort);

  z3::expr_map a(ctx);
  a.insert(x1, x2);
  a.insert(x2, x3);

  std::cout << a << std::endl;
  std::cout << a.find(x1) << std::endl;
  std::cout << a.find(x2) << std::endl;
  try {
    std::cout << a.find(x3) << std::endl;
  }
  catch(z3::exception const & e){
    std::cout << e << std::endl;
  }

  std::cout << a.contains(x1) << std::endl;
  std::cout << a.contains(x2) << std::endl;
  std::cout << a.contains(x3) << std::endl;
}

int main(){

  z3::context ctx;
  z3::sort int_sort = ctx.int_sort();
  z3::sort bool_sort= ctx.bool_sort();

  z3::expr x = ctx.constant("x", int_sort);
  z3::func_decl p = ctx.function("p", int_sort, bool_sort);

  z3::expr_vector example_3(ctx);
  example_3.push_back(1 == x || 2 == x);
  example_3.push_back(p(x));
  example_3.push_back(not(p(1)));
  example_3.push_back(not(p(2)));

  CDCL_T test(example_3);
  test.toDimacsFile();

  return 0;
}
