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

static void print_model(msat_env env);
void email1();
void email2();
void email3();

int main(){
  printf("Example 1\n"); 
  email1();
  printf("Example 2\n");
  email2();
  printf("Example 3\n");
  email3();
  return 0;
}

static void print_model(msat_env env)
{
  /* we use a model iterator to retrieve the model values for all the
   * variables, and the necessary function instantiations */
  msat_model_iterator iter = msat_create_model_iterator(env);
  assert(!MSAT_ERROR_MODEL_ITERATOR(iter));

  printf("Model:\n");
  while (msat_model_iterator_has_next(iter)) {
    msat_term t, v;
    char *s;
    msat_model_iterator_next(iter, &t, &v);
    s = msat_term_repr(t);
    assert(s);
    printf(" %s = ", s);
    msat_free(s);
    s = msat_term_repr(v);
    assert(s);
    printf("%s\n", s);
    msat_free(s);
  }
  msat_destroy_model_iterator(iter);
}

void email1(){
  msat_config cfg;
  msat_env env;
  msat_term formula;
  const char *vars[] = {"x1", "y1", "y2", "y3", "x1"};
  const char *ufs[] = {"f", "g"};
  unsigned int i;
  int res, group_a, group_b;
  msat_type tp, func_tp;
  msat_type paramtps[1];

  printf("\nInterpolation example\n");

  cfg = msat_create_config();
  /* enable interpolation support */
  msat_set_option(cfg, "interpolation", "true");
  msat_set_option(cfg, "model_generation", "true");
    
  env = msat_create_env(cfg);
  assert(!MSAT_ERROR_ENV(env));

  /* the configuration can be deleted as soon as the evironment has been
   * created */
  msat_destroy_config(cfg);

  tp = msat_get_simple_type(env, "X");
  paramtps[0] = tp;
  func_tp = msat_get_function_type(env, paramtps, 1, tp);

  /* declare variables/functions */
  for (i = 0; i < sizeof(vars)/sizeof(vars[0]); ++i) {
    msat_decl d = msat_declare_function(env, vars[i], tp);
    assert(!MSAT_ERROR_DECL(d));
  }
  for (i = 0; i < sizeof(ufs)/sizeof(ufs[0]); ++i) {
    msat_decl d = msat_declare_function(env, ufs[i], func_tp);
    assert(!MSAT_ERROR_DECL(d));
  }

  /* now create the interpolation groups representing the two formulas A and
   * B */
  group_a = msat_create_itp_group(env);
  group_b = msat_create_itp_group(env);
  assert(group_a != -1 && group_b != -1);
    
  /* create and assert formula A */
  formula = msat_from_string(env, "(and (= (f x1) y1) (= (g y2) y3) (= (g y3) x1))");
  assert(!MSAT_ERROR_TERM(formula));

  /* tell MathSAT that all subsequent formulas belong to group A */
  res = msat_set_itp_group(env, group_a);
  assert(res == 0);
  res = msat_assert_formula(env, formula);
  assert(res == 0);
  {
    char *s = msat_term_repr(formula);
    assert(s);
    printf("Asserted formula A (in group %d): %s\n", group_a, s);
    msat_free(s);
  }

  /* create and assert formula B */
  formula = msat_from_string(env, "(and (not (= (f y3) y1)) (= y2 y3) )");
  assert(!MSAT_ERROR_TERM(formula));

  /* tell MathSAT that all subsequent formulas belong to group B */
  res = msat_set_itp_group(env, group_b);
  assert(res == 0);
  res = msat_assert_formula(env, formula);
  assert(res == 0);
  {
    char *s = msat_term_repr(formula);
    assert(s);
    printf("Asserted formula B (in group %d): %s\n", group_b, s);
    msat_free(s);
  }

  
  if(msat_solve(env) == MSAT_SAT){
    print_model(env);
  }
  else{
    if (msat_solve(env) == MSAT_UNSAT) {
      int groups_of_a[1];
      msat_term interpolant;
      char *s;
      groups_of_a[0] = group_a;
      interpolant = msat_get_interpolant(env, groups_of_a, 1);
      assert(!MSAT_ERROR_TERM(interpolant));
      s = msat_term_repr(interpolant);
      assert(s);
      printf("\nOK, the interpolant is: %s\n", s);
      msat_free(s);
    }
    else {
      assert(0 && "should not happen!");
    }

    msat_destroy_env(env);

    printf("\nInterpolation example done\n");
  }
}

void email2(){
  msat_config cfg;
  msat_env env;
  msat_term formula;
  const char *vars[] = {"x1", "y1", "y2", "y3", "x1"};
  const char *ufs[] = {"f", "g"};
  unsigned int i;
  int res, group_a, group_b;
  msat_type tp, func_tp;
  msat_type paramtps[1];

  printf("\nInterpolation example\n");

  cfg = msat_create_config();
  /* enable interpolation support */
  msat_set_option(cfg, "interpolation", "true");
  msat_set_option(cfg, "model_generation", "true");
    
  env = msat_create_env(cfg);
  assert(!MSAT_ERROR_ENV(env));

  /* the configuration can be deleted as soon as the evironment has been
   * created */
  msat_destroy_config(cfg);

  tp = msat_get_simple_type(env, "X");
  paramtps[0] = tp;
  func_tp = msat_get_function_type(env, paramtps, 1, tp);

  /* declare variables/functions */
  for (i = 0; i < sizeof(vars)/sizeof(vars[0]); ++i) {
    msat_decl d = msat_declare_function(env, vars[i], tp);
    assert(!MSAT_ERROR_DECL(d));
  }
  for (i = 0; i < sizeof(ufs)/sizeof(ufs[0]); ++i) {
    msat_decl d = msat_declare_function(env, ufs[i], func_tp);
    assert(!MSAT_ERROR_DECL(d));
  }

  /* now create the interpolation groups representing the two formulas A and
   * B */
  group_a = msat_create_itp_group(env);
  group_b = msat_create_itp_group(env);
  assert(group_a != -1 && group_b != -1);
    
  /* create and assert formula A */
  formula = msat_from_string(env, "(and (= (f x1) y1) (= (g y2) y3) (= (g y3) x1) (= (f x1) y2))");
  assert(!MSAT_ERROR_TERM(formula));

  /* tell MathSAT that all subsequent formulas belong to group A */
  res = msat_set_itp_group(env, group_a);
  assert(res == 0);
  res = msat_assert_formula(env, formula);
  assert(res == 0);
  {
    char *s = msat_term_repr(formula);
    assert(s);
    printf("Asserted formula A (in group %d): %s\n", group_a, s);
    msat_free(s);
  }

  /* create and assert formula B */
  formula = msat_from_string(env, "(and (not (= (f y3) y1)) (= y2 y3) )");
  assert(!MSAT_ERROR_TERM(formula));

  /* tell MathSAT that all subsequent formulas belong to group B */
  res = msat_set_itp_group(env, group_b);
  assert(res == 0);
  res = msat_assert_formula(env, formula);
  assert(res == 0);
  {
    char *s = msat_term_repr(formula);
    assert(s);
    printf("Asserted formula B (in group %d): %s\n", group_b, s);
    msat_free(s);
  }

  
  if(msat_solve(env) == MSAT_SAT){
    print_model(env);
  }
  else{
    if (msat_solve(env) == MSAT_UNSAT) {
      int groups_of_a[1];
      msat_term interpolant;
      char *s;
      groups_of_a[0] = group_a;
      interpolant = msat_get_interpolant(env, groups_of_a, 1);
      assert(!MSAT_ERROR_TERM(interpolant));
      s = msat_term_repr(interpolant);
      assert(s);
      printf("\nOK, the interpolant is: %s\n", s);
      msat_free(s);
    }
    else {
      assert(0 && "should not happen!");
    }

    msat_destroy_env(env);

    printf("\nInterpolation example done\n");
  }
}

void email3(){
  msat_config cfg;
  msat_env env;
  msat_term formula;
  const char *vars[] = {"x1", "y1", "y2", "y3", "x1"};
  const char *ufs[] = {"f", "g"};
  unsigned int i;
  int res, group_a, group_b;
  msat_type tp, func_tp;
  msat_type paramtps[1];

  printf("\nInterpolation example\n");

  cfg = msat_create_config();
  /* enable interpolation support */
  msat_set_option(cfg, "interpolation", "true");
  msat_set_option(cfg, "model_generation", "true");
    
  env = msat_create_env(cfg);
  assert(!MSAT_ERROR_ENV(env));

  /* the configuration can be deleted as soon as the evironment has been
   * created */
  msat_destroy_config(cfg);

  tp = msat_get_simple_type(env, "X");
  paramtps[0] = tp;
  func_tp = msat_get_function_type(env, paramtps, 1, tp);

  /* declare variables/functions */
  for (i = 0; i < sizeof(vars)/sizeof(vars[0]); ++i) {
    msat_decl d = msat_declare_function(env, vars[i], tp);
    assert(!MSAT_ERROR_DECL(d));
  }
  for (i = 0; i < sizeof(ufs)/sizeof(ufs[0]); ++i) {
    msat_decl d = msat_declare_function(env, ufs[i], func_tp);
    assert(!MSAT_ERROR_DECL(d));
  }

  /* now create the interpolation groups representing the two formulas A and
   * B */
  group_a = msat_create_itp_group(env);
  group_b = msat_create_itp_group(env);
  assert(group_a != -1 && group_b != -1);
    
  /* create and assert formula A */
  formula = msat_from_string(env, "(and (= (f x1) y1) (= (g y2) y3) (= (g y3) x1) (= (f x1) y2))");
  assert(!MSAT_ERROR_TERM(formula));

  /* tell MathSAT that all subsequent formulas belong to group A */
  res = msat_set_itp_group(env, group_a);
  assert(res == 0);
  res = msat_assert_formula(env, formula);
  assert(res == 0);
  {
    char *s = msat_term_repr(formula);
    assert(s);
    printf("Asserted formula A (in group %d): %s\n", group_a, s);
    msat_free(s);
  }

  /* create and assert formula B */
  formula = msat_from_string(env, "(and (not (= (f y3) y3)) (= y2 y3) )");
  assert(!MSAT_ERROR_TERM(formula));

  /* tell MathSAT that all subsequent formulas belong to group B */
  res = msat_set_itp_group(env, group_b);
  assert(res == 0);
  res = msat_assert_formula(env, formula);
  assert(res == 0);
  {
    char *s = msat_term_repr(formula);
    assert(s);
    printf("Asserted formula B (in group %d): %s\n", group_b, s);
    msat_free(s);
  }

  
  if(msat_solve(env) == MSAT_SAT){
    print_model(env);
  }
  else{
    if (msat_solve(env) == MSAT_UNSAT) {
      int groups_of_a[1];
      msat_term interpolant;
      char *s;
      groups_of_a[0] = group_a;
      interpolant = msat_get_interpolant(env, groups_of_a, 1);
      assert(!MSAT_ERROR_TERM(interpolant));
      s = msat_term_repr(interpolant);
      assert(s);
      printf("\nOK, the interpolant is: %s\n", s);
      msat_free(s);
    }
    else {
      assert(0 && "should not happen!");
    }

    msat_destroy_env(env);

    printf("\nInterpolation example done\n");
  }
}
