/*
 * api_example.c: A simple example of usage of the MathSAT API
 * author: Alberto Griggio <griggio@fbk.eu>
 *
 * to compile: gcc api_example.c -I${MSAT_DIR}/include -L${MSAT_DIR}/lib
 *             -lmathsat -lgmpxx -lgmp -lstdc++ -o api_example
 */

// Compiled with:
// gcc computingInterpolants.c -lmathsat -lgmpxx -lgmp -lstdc++ -o computingInterpolants

#include <stdio.h>
#include <assert.h>
#include <stdlib.h>
#include <mathsat.h>

int main(){

  msat_config cfg;
  msat_env env;
  msat_term formula;
  const char *vars[] = {"x1", "x2", "x3", "y1", "y2", "y3", "b"};
  const char *ufs[] = {"f", "g"};
  unsigned int i;
  int res, group_a, group_b;
  msat_type rat_tp, func_tp;
  msat_type paramtps[1];

  cfg = msat_create_config();
  /* enable interpolation support */
  msat_set_option(cfg, "interpolation", "true");
  env = msat_create_env(cfg);
  assert(!MSAT_ERROR_ENV(env));
  /* the configuration can be deleted as soon as the evironment has been
   * created */
  msat_destroy_config(cfg);
  rat_tp = msat_get_rational_type(env);
  paramtps[0] = rat_tp;
  func_tp = msat_get_function_type(env, paramtps, 1, rat_tp);

  /* declare variables/functions */
  for (i = 0; i < sizeof(vars)/sizeof(vars[0]); ++i) {
    msat_decl d = msat_declare_function(env, vars[i], rat_tp);
    assert(!MSAT_ERROR_DECL(d));
  }
  for (i = 0; i < sizeof(ufs)/sizeof(ufs[0]); ++i) {
    msat_decl d = msat_declare_function(env, ufs[i], func_tp);
    assert(!MSAT_ERROR_DECL(d));
  }
    
  /* create and assert formula */
  
  formula = msat_from_string(env, "(and (= (+ (f x1) x2) x3) (= (+ (f y1) y2) y3) (<= y1 x1))");
  assert(!MSAT_ERROR_TERM(formula));
  printf("%s\n", msat_term_repr(formula));
  printf("%ld\n", msat_term_id(formula));
  printf("%s\n", msat_term_repr(msat_term_get_arg(formula, 0)));
  
  formula = msat_from_string(env, "(and (= (+ x1 x1) x3))");
  assert(!MSAT_ERROR_TERM(formula));
  printf("%s\n", msat_term_repr(formula));
  printf("%ld\n", msat_term_id(formula));
  printf("%s\n", msat_term_repr(msat_term_get_arg(formula, 0)));

  formula = msat_from_string(env, "(and (= (+ x1 (f (f x1))) x3))");
  assert(!MSAT_ERROR_TERM(formula));
  printf("%s\n", msat_term_repr(formula));
  printf("%ld\n", msat_term_id(formula));
  printf("%s\n", msat_term_repr(msat_term_get_arg(formula, 0)));

  /*
  unsigned long b = msat_num_backtrack_points(env);
  msat_term * a = msat_get_asserted_formulas(env, &b);
  printf("%ld\n", b);
  printf("%s\n", msat_term_repr(*(a)));
  //printf("%s\n", msat_term_repr(a));
  */

  return 0;
}
