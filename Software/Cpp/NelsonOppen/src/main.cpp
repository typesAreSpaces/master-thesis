#include "ThCombInterpolator.h"
#define _DEBUG_ true

void check_implied_equalities(z3::expr_vector & v, z3::solver & s){
  unsigned num = v.size();
  Z3_ast   terms[num];
  unsigned class_ids[num];
  
  for(unsigned i = 0; i < num; i++){
    terms[i] = v[i];
    class_ids[i] = 0;
  }
  
  Z3_get_implied_equalities(v.ctx(), s, num, terms, class_ids);

  for(unsigned i = 0; i < 3; i++)
    std::cout << "Class " << Z3_ast_to_string(v.ctx(), terms[i])
	      << " -> " << class_ids[i] << std::endl;
}

int main(){
  
  z3::set_param("proof", true);
  z3::set_param("pp.single_line", true);
  z3::context ctx;
  
  z3::sort int_sort = ctx.int_sort();
  z3::expr x1 = ctx.constant("x1", int_sort);
  z3::expr x2 = ctx.constant("x2", int_sort);
  z3::expr x3 = ctx.constant("x3", int_sort);
  z3::func_decl g = ctx.function("g", int_sort, int_sort);
 
  z3::func_decl f1 = ctx.function("f", int_sort, int_sort);
  z3::expr formula1 = x1 <= f1(x1);
  z3::expr formula2 = x2 >= x1 && (x1 - x3) >= x2 && x3 >= 0 && f1(f1(x1) - f1(x2)) != f1(x3);
  z3::expr formula3 = g(f1(x1 - 2)) == x1 + 2 && g(f1(x2)) == x2 - 2 && (x2 + 1 == x1 - 1);
  
  z3::func_decl f2 = ctx.function("f", int_sort, int_sort, int_sort);
  z3::expr formula4 = f2(x1, 0) >= x3
    && f2(x2, 0) <= x3
    && x1 >= x2
    && x2 >= x1
    && (x3 - f2(x1, 0) >= 1);
 
  // z3::expr & formula_current_test = formula4;
  
  // Thcombinterpolator p = ThCombInterpolator(formula_current_test);

  // p.collectEqualities();
  // std::cout << p << std::endl;

  z3::solver s(ctx, "QF_UFLIA");
  s.add(x1 >= x2);
  s.add(x2 >= x1);
  
  // Z3_ast terms[3];
  // terms[0] = x1;
  // terms[1] = x2;
  // terms[2] = x3;
  z3::expr_vector terms(ctx);
  terms.push_back(x1);
  terms.push_back(x2);
  terms.push_back(x3);

  // unsigned class_ids[3];
  // class_ids[0] = 0;
  // class_ids[1] = 0;
  // class_ids[2] = 0;
  
  // Z3_get_implied_equalities(ctx, s, 3, terms, class_ids);

  // for(unsigned i = 0; i < 3; i++)
  //   std::cout << "Class " << Z3_ast_to_string(ctx, terms[i]) << " -> " << class_ids[i] << std::endl;

  check_implied_equalities(terms, s);

  // auto aaa = get_enode(formula3);
  
  return 0;
}
