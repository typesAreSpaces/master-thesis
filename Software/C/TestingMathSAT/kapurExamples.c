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
void exampleEUF31();
void exampleEUF43();
void exampleEUF4();
void newExample();
void newExamples(char*, char*);
void exampleOctagon426();
void exampleOctagon417();
void exampleOctagon420();
void exampleOctagon422();
void exampleOctagon4();
void exampleOctagon424();

int main(){
  /*
  printf("Example EUF 31\n");
  exampleEUF31();
  printf("\nExample EUF 43\n");
  exampleEUF43();
  printf("\nExample EUF 4\n");
  exampleEUF4();
  printf("\nExample Octagon 426\n");
  exampleOctagon426();
  printf("\nExample Octagon 417\n");
  exampleOctagon417();
  printf("\nExample Octagon 420\n");
  exampleOctagon420();
  printf("\nExample Octagon 422\n");
  exampleOctagon422();
  printf("\nExample Octagon 4\n");
  exampleOctagon4();
  printf("\nExample Octagon 424\n");
  exampleOctagon424();
  */
  newExample();
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

void exampleEUF31(){
  msat_config cfg;
  msat_env env;
  msat_term formula;
  const char *vars[] = {"x1", "z1", "z2", "x2", "z3", "x3", "z4", "y1", "y2", "y3"};
  const char *ufs[] = {"f"};
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
  formula = msat_from_string(env, "(and (= z1 x1) (= x1 z2) (= z2 x2) (= x2 (f z3)) (= (f z3) x3) (= x3 z4) (= (f z2) x2) (= x2 z3))");
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
  formula = msat_from_string(env, "(and (= z1 y1) (= y1 (f z2)) (= (f z2) y2) (= y2 z3) (= z3 y3) (= z2 y2) (= y2 (f z3)) (not (= y3 z4)))");
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

void exampleEUF43(){
  msat_config cfg;
  msat_env env;
  msat_term formula;
  const char *vars[] = {"x1", "x2", "x3", "x4", "z1", "z2", "z3", "z4", "z5", "z6", "z7", "z8", "y1", "y2"};
  const char *ufs[] = {"f"};
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
  formula = msat_from_string(env, "(and (= x1 z1) (= z2 x2) (= z3 (f x1)) (= (f x2) z4) (= x3 z5) (= z6 x4) (= z7 (f x3)) (= (f x4) z8))");
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
  formula = msat_from_string(env, "(and (= z1 z2) (= z5 (f z3)) (= (f z4) z6) (= y1 z7) (= z8 y2) (not (= y1 y2)))");
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

void exampleEUF4(){
  msat_config cfg;
  msat_env env;
  msat_term formula;
  const char *vars[] = {"x1", "x2", "z1", "z2", "z3", "z4", "y1", "y2", "y3"};
  const char *ufs[] = {"f"};
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
  formula = msat_from_string(env, "(and (= x1 z1) (= z3 (f x1)) (= (f z2) x2) (= x2 z4))");
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
  formula = msat_from_string(env, "(and (= z1 y1) (= y1 z2) (= y2 z3) (= z4 y3) (not (= (f y2) (f y3))))");
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

void newExamples(char* agroup, char* bgroup){
  msat_config cfg;
  msat_env env;
  msat_term formula;
  const char *vars[] = {"a", "b", "c", "d", "u", "v", "w"};
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
  formula = msat_from_string(env, agroup);
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
  formula = msat_from_string(env, bgroup);
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

void newExample(){
  //1expr B = (b == d) && !(c == d);
  //expr B = (g(b) == g(d)) && !(c == d) && (g(a) == g(d));
  //1expr B = (b == d) && !(c == d);
  //1expr B = (a == d) && (b == c) && !(c == d);
  //1expr B = ((a == d) && (b == c) && !(c == d)) || ((b == d) && !(c == d));
  printf("Example 1\n");
  newExamples("(and (= (f a) u) (= (f b) c) (= (f c) u) (= (f d) d))", "(and (= b d) (not (= c d)))");
  printf("Example 2\n");
  newExamples("(and (= (f a) u) (= (f b) c) (= (f c) u) (= (f d) d))", "(and (= (g b) (g d)) (not (= c d)) (= (g a) (g d)))");
  printf("Example 3\n");
  newExamples("(and (= (f a) u) (= (f b) c) (= (f c) u) (= (f d) d))", "(and (= a d) (= b c) (not (= c d)))");
  printf("Example 4\n");
  newExamples("(and (= (f a) u) (= (f b) c) (= (f c) u) (= (f d) d))", "(or (and (= a d) (= b c) (not (= c d))) (and (= b d) (not (= c d))))");
  printf("Example 5\n");
  newExamples("(and (= (f a) u) (= (f b) c) (= (f c) u) (= (f d) d))", "(and (= (g a) v) (= (g d) w) (= (g v) b) (= (g w) c) (= a d) (not (= c d)))");
  
}

void exampleOctagon426(){
  msat_config cfg;
  msat_env env;
  msat_term formula;
  const char *vars[] = {"x1", "x2", "x3", "x4", "x5", "x6"};
  unsigned int i;
  int res, group_a, group_b;
  msat_type tp;
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

  tp = msat_get_integer_type(env);
  paramtps[0] = tp;

  /* declare variables/functions */
  for (i = 0; i < sizeof(vars)/sizeof(vars[0]); ++i) {
    msat_decl d = msat_declare_function(env, vars[i], tp);
    assert(!MSAT_ERROR_DECL(d));
  }

  /* now create the interpolation groups representing the two formulas A and
   * B */
  group_a = msat_create_itp_group(env);
  group_b = msat_create_itp_group(env);
  assert(group_a != -1 && group_b != -1);
    
  /* create and assert formula A */
  formula = msat_from_string(env, "(and (>= (- x1 x2) (- 4)) (>= (- (- x2) x3) 5) (>= (+ x2 x6) 4) (>= (+ x2 x5) (- 3)))");
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
  formula = msat_from_string(env, "(and (>= (+ (- x1) x3) (- 2)) (>= (- (- x4) x6) 0) (>= (+ (- x5) x4) 0))");
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

void exampleOctagon417(){
  msat_config cfg;
  msat_env env;
  msat_term formula;
  const char *vars[] = {"x1", "x2", "x3", "x4", "x5", "x6"};
  unsigned int i;
  int res, group_a, group_b;
  msat_type tp;
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

  tp = msat_get_integer_type(env);
  paramtps[0] = tp;

  /* declare variables/functions */
  for (i = 0; i < sizeof(vars)/sizeof(vars[0]); ++i) {
    msat_decl d = msat_declare_function(env, vars[i], tp);
    assert(!MSAT_ERROR_DECL(d));
  }

  /* now create the interpolation groups representing the two formulas A and
   * B */
  group_a = msat_create_itp_group(env);
  group_b = msat_create_itp_group(env);
  assert(group_a != -1 && group_b != -1);
    
  /* create and assert formula A */
  formula = msat_from_string(env, "(and (>= (+ (- x2) (- x1) 3) 0) (>= (+ x1 x3 1) 0) (>= (+ (- x3) (- x4) (- 6)) 0) (>= (+ x5 x4 1) 0))");
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
  formula = msat_from_string(env, "(and (>= (+ x2 x3 3) 0) (>= (+ x6 (- x5) (- 1)) 0) (>= (+ x4 (- x6) 4) 0))");
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

void exampleOctagon420(){
  msat_config cfg;
  msat_env env;
  msat_term formula;
  const char *vars[] = {"x1", "x2", "x3", "x4", "x5", "x6"};
  unsigned int i;
  int res, group_a, group_b;
  msat_type tp;
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

  tp = msat_get_integer_type(env);
  paramtps[0] = tp;

  /* declare variables/functions */
  for (i = 0; i < sizeof(vars)/sizeof(vars[0]); ++i) {
    msat_decl d = msat_declare_function(env, vars[i], tp);
    assert(!MSAT_ERROR_DECL(d));
  }

  /* now create the interpolation groups representing the two formulas A and
   * B */
  group_a = msat_create_itp_group(env);
  group_b = msat_create_itp_group(env);
  assert(group_a != -1 && group_b != -1);
    
  /* create and assert formula A */
  formula = msat_from_string(env, "(and (>= (- x3 x1) (- 2)) (>= (- (- x6) x4) 0) (>= (- x4 x5) 0))");
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
  formula = msat_from_string(env, "(and (>= (- x1 x2) (- 4)) (>= (- (- x2) x3) 5) (>= (+ x2 x6) 4) (>= (+ x2 x5) (- 3)))");
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

void exampleOctagon422(){
  msat_config cfg;
  msat_env env;
  msat_term formula;
  const char *vars[] = {"x1", "x2", "x3", "x4", "x5", "x6"};
  unsigned int i;
  int res, group_a, group_b;
  msat_type tp;
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

  tp = msat_get_integer_type(env);
  paramtps[0] = tp;

  /* declare variables/functions */
  for (i = 0; i < sizeof(vars)/sizeof(vars[0]); ++i) {
    msat_decl d = msat_declare_function(env, vars[i], tp);
    assert(!MSAT_ERROR_DECL(d));
  }

  /* now create the interpolation groups representing the two formulas A and
   * B */
  group_a = msat_create_itp_group(env);
  group_b = msat_create_itp_group(env);
  assert(group_a != -1 && group_b != -1);
    
  /* create and assert formula A */
  formula = msat_from_string(env, "(and (>= (- x1 x2) (- 4)) (>= (+ x2 x6) 4) (>= (- (- x4) x6) 0) (>= (+ (- x1) x3) (- 2)))");
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
  formula = msat_from_string(env, "(and (>= (- (- x2) x3) 5) (>= (+ x2 x5) (- 3)) (>= (- x4 x5) 0))");
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

void exampleOctagon4(){
  msat_config cfg;
  msat_env env;
  msat_term formula;
  const char *vars[] = {"x1", "x2", "x3", "x4", "x5", "x6"};
  unsigned int i;
  int res, group_a, group_b;
  msat_type tp;
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

  tp = msat_get_integer_type(env);
  paramtps[0] = tp;

  /* declare variables/functions */
  for (i = 0; i < sizeof(vars)/sizeof(vars[0]); ++i) {
    msat_decl d = msat_declare_function(env, vars[i], tp);
    assert(!MSAT_ERROR_DECL(d));
  }

  /* now create the interpolation groups representing the two formulas A and
   * B */
  group_a = msat_create_itp_group(env);
  group_b = msat_create_itp_group(env);
  assert(group_a != -1 && group_b != -1);
    
  /* create and assert formula A */
  formula = msat_from_string(env, "(and (>= (- x1 x2) (- 4)) (>= (+ x2 x6) 4) (>= (+ (- x1) x3) (- 2)) (>= (- (- x2) x3) 5))");
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
  formula = msat_from_string(env, "(and (>= (+ x2 x5) (- 3)) (>= (+ (- x5) x4) 0) (>= (- (- x4) x6) 0))");
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

void exampleOctagon424(){
  msat_config cfg;
  msat_env env;
  msat_term formula;
  const char *vars[] = {"x1", "x2", "x3", "x4", "x5", "x6"};
  unsigned int i;
  int res, group_a, group_b;
  msat_type tp;
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

  tp = msat_get_integer_type(env);
  paramtps[0] = tp;

  /* declare variables/functions */
  for (i = 0; i < sizeof(vars)/sizeof(vars[0]); ++i) {
    msat_decl d = msat_declare_function(env, vars[i], tp);
    assert(!MSAT_ERROR_DECL(d));
  }

  /* now create the interpolation groups representing the two formulas A and
   * B */
  group_a = msat_create_itp_group(env);
  group_b = msat_create_itp_group(env);
  assert(group_a != -1 && group_b != -1);
    
  /* create and assert formula A */
  formula = msat_from_string(env, "(and (>= (- x1 x2) (- 4)) (>= (+ x2 x6) 4) (>= (+ (- x1) x3) (- 2)) (>= (- (- x2) x3) 5) (>= (+ x2 x5) (- 3)))");
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
  formula = msat_from_string(env, "(and (>= (- (- x6) x4) 0) (>= (- x4 x5) 0))");
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
