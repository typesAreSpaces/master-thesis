
#include "ThCombInterpolator.h"
#include <string>
#define _DEBUG_ true

void check_implied_equalities(z3::expr_vector & v, z3::solver & s){
  unsigned num = v.size();
  Z3_ast   terms[num];
  unsigned class_ids[num];
  
  for(unsigned i = 0; i < num; i++){
    terms[i] = v[i];
    class_ids[i] = 0;
  }
  
  auto check = Z3_get_implied_equalities(v.ctx(), s, num, terms, class_ids);

  switch(check){
  case Z3_L_TRUE:
    std::cout << "sat" << std::endl;
    for(unsigned i = 0; i < num; i++)
      std::cout << "Class " << Z3_ast_to_string(v.ctx(), terms[i])
		<< " -> " << class_ids[i] << std::endl;
    break;
  case Z3_L_FALSE:
    std::cout << "unsat" << std::endl;
    break;
  case Z3_L_UNDEF:
    std::cout << "unknown" << std::endl;
    break;
  }
}

int main(){
  
  z3::set_param("proof", true);
  // z3::set_param("pp.single_line", true);
  // z3::set_param("pp.pretty_proof", true);
  z3::set_param("pp.min_alias_size", 10000000);
  z3::context ctx;
  
  z3::sort int_sort = ctx.int_sort();
  z3::sort bool_sort = ctx.bool_sort();
  z3::expr x1 = ctx.constant("x1", int_sort);
  z3::expr x2 = ctx.constant("x2", int_sort);
  z3::expr x3 = ctx.constant("x3", int_sort);
  z3::expr y1 = ctx.constant("y1", int_sort);
  z3::expr y2 = ctx.constant("y2", int_sort);
  z3::expr y3 = ctx.constant("y3", int_sort);
  z3::expr a1 = ctx.constant("a1", int_sort);
  z3::expr a2 = ctx.constant("a2", int_sort);
  z3::expr a = ctx.constant("a", int_sort);
  z3::expr b = ctx.constant("b", int_sort);
  z3::func_decl g = ctx.function("g", int_sort, int_sort);
  z3::func_decl f1 = ctx.function("f", int_sort, int_sort);
  z3::func_decl f2 = ctx.function("f", int_sort, int_sort, int_sort);
  z3::func_decl p = ctx.function("p", int_sort, bool_sort);
  
  z3::expr formula1 = x1 <= f1(x1) && x2 == x3;
  z3::expr formula2 = x2 >= x1 && (x1 - x3) >= x2 && x3 >= 0 && f1(f1(x1) - f1(x2)) != f1(x3);
  z3::expr formula3 = g(f1(x1 - 2)) == x1 + 2 && g(f1(x2)) == x2 - 2 && (x2 + 1 == x1 - 1);
 
  z3::expr formula4 = f2(x1, 0) >= x3
    && f2(x2, 0) <= x3
    && x1 >= x2
    && x2 >= x1
    && (x3 - f2(x1, 0) >= 1);
  z3::expr formula5 = f2(x1, 0) >= x3
    && f2(x2, 0) <= x3
    && x1 >= x2 + 0
    && 4*x1 + 5*x2 <= 23
    && -5*x1 - 5*x3 > 21
    && x2 >= x1
    && (x3 - f2(x1, 0) >= 1);

  z3::expr formula_a = f1(x1) + x2 == x3 && y3 == f1(y1) + y2 && y1 <= x1;
  z3::expr formula_b = x2 == g(b) && y2 == g(b) && x1 <= y1 && x3 < y3;
  
  ThCombInterpolator test = ThCombInterpolator(ctx, formula_a, formula_b);
  std::cout << test << std::endl;

  z3::solver s(ctx, "QF_UFLIA");
  // s.add(1 <= x1);
  // s.add(x1 <= 2);
  // s.add(a1 == 1);
  // s.add(a2 == 2);
  // s.add(p(x1));
  // s.add(not(p(a1)));
  // s.add(not(p(a2)));
  s.add(formula_a);
  s.add(formula_b);
  if(s.check() == z3::unsat)
    std::cout << s.proof() << std::endl;
  
  // z3::expr_vector terms(ctx);
  // terms.push_back(x1);
  // terms.push_back(x2);
  // terms.push_back(x3);

  // check_implied_equalities(terms, s);
  
  return 0;
}
