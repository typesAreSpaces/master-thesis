/*++
  Copyright (c) 2015 Microsoft Corporation

  --*/

#include<vector>
#include"z3++.h"

using namespace z3;

void prove_example1();
void interpolant_example1();
void interpolant_example2();
void interpolant_example3();
void sequence_interpolants_example();
void tree_interpolants_example();
void kapur_example_1();
void kapur_example_1a();

int main() {

  try {
    //prove_example1();
    //interpolant_example1();
    //interpolant_example2();
    //std::cout << "\n";
    //sequence_interpolants_example();
    //std::cout << "\n";
    //tree_interpolants_example();
    //std::cout << "\n";
    //kapur_example_1();
    //std::cout << "\n";
    //kapur_example_1a();
    //std::cout << "\n";
    //interpolant_example3();
    context c;
    Z3_ast a = Z3_parse_smtlib2_string(c, "(and p q)", 0, 0, 0, 0, 0, 0);
    //std::cout << a;
    
    std::cout << "\n";
  }
  catch (exception & ex) {
    std::cout << "unexpected error: " << ex << "\n";
  }
    
  return 0;
}

void prove_example1() {
  std::cout << "prove_example1\n";
    
  context c;
  sort A      = c.uninterpreted_sort("A");
  expr x      = c.constant("x", A);
  expr y      = c.constant("y", A);
  
  func_decl g = c.function("g", A, A);
    
  solver s(c);
  expr conjecture1 = implies(x == y, g(x) == g(y));
  std::cout << "conjecture 1\n" << conjecture1 << "\n";
  s.add(!conjecture1);
  if (s.check() == unsat) 
    std::cout << "proved" << "\n";
  else
    std::cout << "failed to prove" << "\n";

  s.reset(); // remove all assertions from solver s

  expr conjecture2 = implies(x == y, g(g(x)) == g(y));
  std::cout << "conjecture 2\n" << conjecture2 << "\n";
  s.add(!conjecture2);
  if (s.check() == unsat) {
    std::cout << "proved" << "\n";
  }
  else {
    std::cout << "failed to prove" << "\n";
    model m = s.get_model();
    std::cout << "counterexample:\n" << m << "\n";
    std::cout << "g(g(x)) = " << m.eval(g(g(x))) << "\n";
    std::cout << "g(y)    = " << m.eval(g(y)) << "\n";
  }
}

void interpolant_example1(){
  std::cout << "interpolant_example1\n";

  context c;
  sort A = c.uninterpreted_sort("A");
  expr x1 = c.constant("x1", A);
  expr x2 = c.constant("x2", A);
  func_decl f = function("f", A, A);
  expr formula = f(x1) != f(x2);
  // TODO: complete an example using functional symbols!
}

void interpolant_example2(){

  z3::config cfg;
  cfg.set("PROOF", true);
  cfg.set("MODEL", true);
  z3::context ctx(cfg);
  expr a = ctx.int_const("a");
  expr b = ctx.int_const("b");
  expr c = ctx.int_const("c");
  expr d = ctx.int_const("d");
  expr A = (a == b) && (a == c);
  expr B = (b == d) && (! (c==d) );
  expr A_ = z3::expr(ctx, Z3_mk_interpolant(ctx, A));
    
  z3::params param_(ctx);
  Z3_ast_vector * vector = new Z3_ast_vector();
  Z3_model * model = new Z3_model();
  Z3_lbool result = Z3_compute_interpolant(ctx, A_ && B, param_, vector, model);

  if (result == Z3_L_TRUE) {
    std::cout << "true" << std::endl;
  } else if (result == Z3_L_FALSE) {
    std::cout << "false" << std::endl;
    std::cout << z3::ast_vector(ctx, *vector);
  } else {
    std::cout << "unknown" << std::endl;
  }
}

void interpolant_example3(){

  z3::config cfg;
  cfg.set("PROOF", true);
  cfg.set("MODEL", true);
  cfg.set("TRACE", true);
  z3::context ctx(cfg);
  sort A1 = ctx.uninterpreted_sort("A");
  expr x1 = ctx.constant("x1", A1);
  expr a = ctx.constant("a", A1);
  expr b = ctx.constant("b", A1);
  expr c = ctx.constant("c", A1);
  expr d = ctx.constant("d", A1);
  expr u = ctx.constant("u", A1);
  expr v = ctx.constant("v", A1);
  expr w = ctx.constant("w", A1);
  func_decl f = function("f", A1, A1);
  func_decl g = function("g", A1, A1);

  expr A = (f(a) == u) && (f(b) == c) && (f(c) == u) && (f(d) == d);
  //1expr B = (b == d) && !(c == d);
  //expr B = (g(b) == g(d)) && !(c == d) && (g(a) == g(d));
  //1expr B = (b == d) && !(c == d);
  //1expr B = (a == d) && (b == c) && !(c == d);
  //1expr B = ((a == d) && (b == c) && !(c == d)) || ((b == d) && !(c == d));
  expr B = (g(a) == v) && (g(d) == w) && (g(v) == b) && (g(w) == c) && (a == d) && (c != d);

  expr A_ = z3::expr(ctx, Z3_mk_interpolant(ctx, A));
    
  z3::params param_(ctx);
  Z3_ast_vector * vector = new Z3_ast_vector();
  Z3_model * model = new Z3_model();
  Z3_lbool result = Z3_compute_interpolant(ctx, A_ && B, param_, vector, model);

  if (result == Z3_L_TRUE) {
    std::cout << "true" << std::endl;
  } else if (result == Z3_L_FALSE) {
    std::cout << "false" << std::endl;
    std::cout << z3::ast_vector(ctx, *vector);
  } else {
    std::cout << "unknown" << std::endl;
  }
}

void sequence_interpolants_example(){
  
  z3::config cfg;
  //cfg.set("PROOF", true); ?
  //cfg.set("MODEL", true);
  z3::context ctx(cfg);
  expr a = ctx.int_const("a");
  expr b = ctx.int_const("b");
  expr c = ctx.int_const("c");
  expr d = ctx.int_const("d");
  expr e = ctx.int_const("e");
  expr A = (a == b) && (a == c);
  expr B = (c == d);
  expr C = (b == e) && !(d == e);
  std::cout << "Here" << std::endl;
  expr A_ = z3::expr(ctx, Z3_mk_interpolant(ctx, A));
  expr AB = A_ && B;
  expr AB_ = z3::expr(ctx, Z3_mk_interpolant(ctx, AB));
  expr ABC = AB_ && C;
  //expr ABC_ = z3::expr(ctx, Z3_mk_interpolant(ctx, ABC));
    
  z3::params param_(ctx);
  Z3_ast_vector * vector = new Z3_ast_vector();
  Z3_model * model = new Z3_model();
  Z3_lbool result = Z3_compute_interpolant(ctx, ABC, param_, vector, model);

  if (result == Z3_L_TRUE) {
    std::cout << "true" << std::endl;
  } else if (result == Z3_L_FALSE) {
    std::cout << "false" << std::endl;
    std::cout << z3::ast_vector(ctx, *vector);
  } else {
    std::cout << "unknown" << std::endl;
  }
}

void tree_interpolants_example(){
  
  z3::config cfg;
  //cfg.set("PROOF", true); ?
  //cfg.set("MODEL", true);
  z3::context ctx(cfg);
  expr a = ctx.int_const("a");
  expr b = ctx.int_const("b");
  expr c = ctx.int_const("c");
  expr d = ctx.int_const("d");
  expr e = ctx.int_const("e");
  expr A = (a == b) && (a == c);
  expr B = (c == d);
  expr C = (b == e) && !(d == e);
  std::cout << "Here" << std::endl;
  expr A_ = z3::expr(ctx, Z3_mk_interpolant(ctx, A));
  expr B_ = z3::expr(ctx, Z3_mk_interpolant(ctx, B));
  expr AB = A_ && B;
  expr AB_ = z3::expr(ctx, Z3_mk_interpolant(ctx, AB));
  expr ABC = AB_ && C;
  //expr ABC_ = z3::expr(ctx, Z3_mk_interpolant(ctx, ABC));
    
  z3::params param_(ctx);
  Z3_ast_vector * vector = new Z3_ast_vector();
  Z3_model * model = new Z3_model();
  Z3_lbool result = Z3_compute_interpolant(ctx, A_ && B_ && C, param_, vector, model);

  if (result == Z3_L_TRUE) {
    std::cout << "true" << std::endl;
  } else if (result == Z3_L_FALSE) {
    std::cout << "false" << std::endl;
    std::cout << z3::ast_vector(ctx, *vector);
  } else {
    std::cout << "unknown" << std::endl;
  }
}

void kapur_example_1(){
  config cfg;
  context ctx(cfg);
  expr x1 = ctx.int_const("x1");
  expr x2 = ctx.int_const("x2");
  expr x3 = ctx.int_const("x3");
  expr x4 = ctx.int_const("x4");
  expr x5 = ctx.int_const("x5");
  expr x6 = ctx.int_const("x6");
  expr A = (x1 - x2 >= -4) && (-x2 - x3 >= 5) && (x2 + x6 >= 4) && (x2 + x5 >= -3);
  expr B = (-x1 + x3 >= -2) && (-x4 - x6 >= 0) && (-x5 + x4 >= 0);
  expr A_ = expr(ctx, Z3_mk_interpolant(ctx, A));
  
  params param_(ctx);
  Z3_ast_vector * vector = new Z3_ast_vector();
  Z3_model * model = new Z3_model();
  Z3_lbool result = Z3_compute_interpolant(ctx, A_ && B, param_, vector, model);

  if (result == Z3_L_TRUE) {
    std::cout << "true" << std::endl;
  } else if (result == Z3_L_FALSE) {
    std::cout << "false" << std::endl;
    std::cout << z3::ast_vector(ctx, *vector);
  } else {
    std::cout << "unknown" << std::endl;
  } 
}

void kapur_example_1a(){
  config cfg;
  context ctx(cfg);
  expr x1 = ctx.int_const("x1");
  expr x2 = ctx.int_const("x2");
  expr x3 = ctx.int_const("x3");
  expr x4 = ctx.int_const("x4");
  expr x5 = ctx.int_const("x5");
  expr x6 = ctx.int_const("x6");
  expr A = (-x2 - x1 + 3 >= 0) && (x1 + x3 + 1 >= 0) && (-x3 - x4 - 6 >= 0) && (x5 + x4 + 1 >= 0);
  expr B = (x2 + x3 + 3 >= 0) && (x6 - x5 - 1 >= 0) && (x4 - x6 + 4 >= 0); 
  expr A_ = expr(ctx, Z3_mk_interpolant(ctx, A));
  
  params param_(ctx);
  Z3_ast_vector * vector = new Z3_ast_vector();
  Z3_model * model = new Z3_model();
  Z3_lbool result = Z3_compute_interpolant(ctx, A_ && B, param_, vector, model);

  if (result == Z3_L_TRUE) {
    std::cout << "true" << std::endl;
  } else if (result == Z3_L_FALSE) {
    std::cout << "false" << std::endl;
    std::cout << z3::ast_vector(ctx, *vector);
  } else {
    std::cout << "unknown" << std::endl;
  }
  
}
