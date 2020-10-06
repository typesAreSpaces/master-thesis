#include <algorithm>
#include <iostream>
#include <fstream>
#include <z3++.h>
#include <set>
#include <vector>
#include <list>
#include <stdio.h>
#include <stdlib.h>
#include <time.h> 
#define DEBUG 1
#define IZ3_PREFIX     "iz3_instance_"
#define MATHSAT_PREFIX "mathsat_instance_"
#define OCTI_PREFIX    "octi_instance_"
#define SMT_SUFFIX     ".smt2"
#define TXT_SUFFIX     ".txt"

class Symbols {

  std::set<std::string> symbols;

  void traverse(z3::expr const &);

  public:
  Symbols(z3::context & ctx, z3::expr_vector const &);

  std::set<std::string> get_symbols() const;
};

class OCTSignature {

  z3::context & ctx;

  std::set<unsigned> ids;
  z3::expr_vector a_part;
  z3::expr_vector b_part;

  bool is_valid_instance;

  unsigned const num_constants;
  unsigned const num_ineqs;
  unsigned const max_limit;
  unsigned const limit_search;
  unsigned num_vars_to_elim;

  void BuildAPart();
  void BuildBPart(z3::solver &);

  public:
  OCTSignature(z3::context &,
      unsigned, unsigned, unsigned, unsigned);

  friend std::ostream & operator << (std::ostream &, OCTSignature const &);

  void iZ3Instance()     const;
  void MathsatInstance() const;
  void OCTIInstance()    const;
  bool IsValidInstance() const;

  void UpdateNumVarsToElim();

  std::string MyName() const;
};

void iZ3Benchmark(z3::context &, z3::sort const &);
void MathsatBenchmark(z3::context &, z3::sort const &);
void OCTIBenchmark(z3::context &, z3::sort const &);

int main(){
  /* initialize random seed: */
  srand(time(NULL));

  z3::context ctx;
  z3::sort sort_A = ctx.uninterpreted_sort("A");

  //iZ3Benchmark(ctx, sort_A);
  MathsatBenchmark(ctx, sort_A);
  //OCTIBenchmark(ctx, sort_A);

  return 0;
}

Symbols::Symbols(z3::context & ctx, z3::expr_vector const & input) : 
  symbols({})
{
  for(auto const & lit : input)
    traverse(lit);
}

void Symbols::traverse(z3::expr const & e){
  if(e.is_app()){
    unsigned num_args = e.num_args();
    std::string f_name = e.decl().name().str();
    if(f_name != "+" 
        && f_name != "-"
        && f_name != "*"
        && f_name != "<="
        && f_name != "Int"
        )
      symbols.insert(f_name);
    for(unsigned i = 0; i < num_args; ++i)
      traverse(e.arg(i));
  }
}

std::set<std::string> Symbols::get_symbols() const {
  return symbols;
}

void OCTSignature::BuildAPart(){
  unsigned counter_a_part = 0;
  while(counter_a_part < num_ineqs){
    int term_1_coeff = rand() % 3 - 1;
    int term_2_coeff = rand() % 3 - 1;
    if(term_1_coeff == 0 && term_2_coeff == 0)
      continue;
    auto const & term_1 = term_1_coeff*ctx.int_const(
        ("x_" + std::to_string(rand() % num_constants)).c_str());
    auto const & term_2 = term_2_coeff*ctx.int_const(
        ("x_" + std::to_string(rand() % num_constants)).c_str());
    auto const & new_lhs = (rand() % 2 == 0) ?
      term_1 + term_2 : term_1 - term_2;
    int rnd_limit = 2*(rand() % max_limit) - max_limit;
    auto const & new_ineq = new_lhs <= rnd_limit;
    if(term_1.id() != term_2.id() 
        && ids.find(new_ineq.id()) == ids.end()){
      ids.insert(new_ineq.id());
      a_part.push_back(new_ineq);
      ++counter_a_part;
    }
  }
}

void OCTSignature::BuildBPart(z3::solver & sol){
  auto current_check = sol.check();
  z3::solver local_sol(ctx);

  unsigned num_iter = 0;

  while(current_check != z3::unsat){
    int term_1_coeff = rand() % 3 - 1;
    int term_2_coeff = rand() % 3 - 1;
    if(term_1_coeff == 0 && term_2_coeff == 0)
      continue;
    auto const & term_1 = term_1_coeff*ctx.int_const(
        ("x_" + std::to_string(rand() % num_constants)).c_str());
    auto const & term_2 = term_2_coeff*ctx.int_const(
        ("x_" + std::to_string(rand() % num_constants)).c_str());
    auto const & new_lhs = (rand() % 2 == 0) ?
      term_1 + term_2 : term_1 - term_2;
    int rnd_limit = 2*(rand() % max_limit) - max_limit;
    auto const & new_ineq = new_lhs <= rnd_limit;
    local_sol.push();
    local_sol.add(new_ineq);
    auto current_local_check = local_sol.check();
    local_sol.pop();
    if(term_1.id() != term_2.id() 
        && ids.find(new_ineq.id()) == ids.end() 
        && current_local_check == z3::sat){
      local_sol.add(new_ineq);
      ids.insert(new_ineq.id());
      b_part.push_back(new_ineq);
      sol.add(new_ineq);
    }

    current_check = sol.check();
    if(++num_iter > limit_search){
#if DEBUG
      std::cout << "Not valid B-part instance" << std::endl;
#endif
      is_valid_instance = false;
      return;
    }
  }
#if DEBUG
  std::cout << "Valid B-part instance" << std::endl;
#endif
}

void OCTSignature::iZ3Instance() const {
  std::ofstream out(IZ3_PREFIX + MyName() + SMT_SUFFIX);
  out << "(set-option :produce-interpolants true)" << std::endl;
  for(unsigned i = 0; i < num_constants; ++i)
    out << "(declare-fun x_" << i << " () Int)" << std::endl;

  out << "(assert (!" << std::endl;
  out << "(and" << std::endl;
  for(auto const & lit : a_part)
    out << lit  << std::endl;
  out << ") :named a_part" << std::endl;
  out << "))" << std::endl;

  out << "(assert (!" << std::endl;
  out << "(and" << std::endl;
  for(auto const & lit : b_part)
    out << lit  << std::endl;
  out << ") :named b_part" << std::endl;
  out << "))" << std::endl;

  out << "(check-sat)" << std::endl;
  out << "(get-interpolant a_part b_part)" << std::endl;

  out.close();
}

void OCTSignature::MathsatInstance() const {
  std::ofstream out(MATHSAT_PREFIX + MyName() + SMT_SUFFIX);
  out << "(set-option :produce-interpolants true)" << std::endl;
  for(unsigned i = 0; i < num_constants; ++i)
    out << "(declare-fun x_" << i << " () Int)" << std::endl;

  out << "(assert (!" << std::endl;
  out << "(and" << std::endl;
  for(auto const & lit : a_part)
    out << lit  << std::endl;
  out << ") :interpolation-group a_part" << std::endl;
  out << "))" << std::endl;

  out << "(assert (!" << std::endl;
  out << "(and" << std::endl;
  for(auto const & lit : b_part)
    out << lit  << std::endl;
  out << ") :interpolation-group b_part" << std::endl;
  out << "))" << std::endl;

  out << "(check-sat)" << std::endl;
  out << "(get-interpolant (a_part))" << std::endl;
  out << "(exit)" << std::endl;

  out.close();
}

void OCTSignature::OCTIInstance() const {
  std::ofstream out(OCTI_PREFIX + MyName() + SMT_SUFFIX);
  for(unsigned i = 0; i < num_constants; ++i)
    out << "(declare-fun x_" << i << " () Int)" << std::endl;

  out << "(assert (and" << std::endl;
  for(auto const & lit : a_part)
    out << lit  << std::endl;
  out << "))" << std::endl;

  out << "(assert (and" << std::endl;
  for(auto const & lit : b_part)
    out << lit  << std::endl;
  out << "))" << std::endl;

  out << "(check-sat)" << std::endl;

  out.close();
}

bool OCTSignature::IsValidInstance() const {
  return is_valid_instance;
}

OCTSignature::OCTSignature(z3::context & ctx, 
    unsigned num_constants,
    unsigned num_ineqs, unsigned max_limit,
    unsigned limit_search
    ) : 
  ctx(ctx), ids({}), a_part(ctx), b_part(ctx),
  is_valid_instance(true),
  num_constants(num_constants), num_ineqs(num_ineqs), 
  max_limit(max_limit), limit_search(limit_search),
  num_vars_to_elim(0)
{

  BuildAPart();

  z3::solver sol(ctx);
  for(auto const & eq : a_part)
    sol.add(eq);
  is_valid_instance = sol.check() == z3::sat;
  if(is_valid_instance){
#if DEBUG
    std::cout << "Valid A-part instance" << std::endl;
#endif
    BuildBPart(sol);
    if(is_valid_instance)
      UpdateNumVarsToElim();
  }
#if DEBUG
  else
    std::cout << "Not valid A-part instance" << std::endl;
#endif
}

std::ostream & operator << (std::ostream & os, OCTSignature const & eufs){
  os << "A part formulas:" << std::endl;
  os << eufs.a_part << std::endl;
  os << "B part formulas:" << std::endl;
  os << eufs.b_part << std::endl;
  return os;
}

void OCTSignature::UpdateNumVarsToElim(){
  std::set<std::string> a_symbols = Symbols(ctx, a_part).get_symbols();
  std::set<std::string> b_symbols = Symbols(ctx, b_part).get_symbols();

#if DEBUG
  std::cout << "Symbols in A-part" << std::endl;
  for(auto const & a : a_symbols)
    std::cout << a << std::endl;
  std::cout << "Symbols in B-part" << std::endl;
  for(auto const & b : b_symbols)
    std::cout << b << std::endl;
#endif

  std::set<std::string> result({});
  std::set_difference(
      a_symbols.begin(), a_symbols.end(),
      b_symbols.begin(), b_symbols.end(),
      std::inserter(result, result.end())
      );
  num_vars_to_elim = result.size();
}

std::string OCTSignature::MyName() const {
  return 
    std::to_string(num_constants) 
    + "_" + std::to_string(num_ineqs)
    + "_" + std::to_string(max_limit)
    + "_" + std::to_string(num_vars_to_elim)
    ;
}

void iZ3Benchmark(z3::context & ctx, z3::sort const & sort_A){
  std::string file_name = "iz3_benchmark.txt";
  system(("rm -rf " + file_name).c_str());

  for(unsigned i = 0; i < 1000; ++i){
    //OCTSignature S(ctx, 
    //num_constants, num_ineqs, max_limit);
    OCTSignature S(ctx, 10, 5, 3, 1000);

    if(!S.IsValidInstance()){
      --i;
      continue;
    }
    S.iZ3Instance();
    system(("echo \"test: " + S.MyName() + "\">> " + file_name).c_str());
    system(("{ time ../../bin/z3-interp " + (IZ3_PREFIX + S.MyName()) + SMT_SUFFIX + "; } 2>> " + file_name).c_str());
    system(("rm " + (IZ3_PREFIX + S.MyName()) + SMT_SUFFIX).c_str());
  }
}

void MathsatBenchmark(z3::context & ctx, z3::sort const & sort_A){
  std::string file_name = "mathsat_benchmark.txt";
  system(("rm -rf " + file_name).c_str());

  for(unsigned i = 0; i < 1000; ++i){
    //OCTSignature S(ctx, 
    //num_constants, num_ineqs, max_limit);
    OCTSignature S(ctx, 10, 5, 3, 1000);
    if(!S.IsValidInstance()){
      --i;
      continue;
    }
    S.MathsatInstance();
    system(("echo \"test: " + S.MyName() + "\">> " + file_name).c_str());
    system(("{ time ../../bin/mathsat " + (MATHSAT_PREFIX + S.MyName()) + SMT_SUFFIX + "; } 2>> " + file_name).c_str());
    system(("rm " + (MATHSAT_PREFIX + S.MyName()) + SMT_SUFFIX).c_str());
  }
}

void OCTIBenchmark(z3::context & ctx, z3::sort const & sort_A){
  std::string file_name = "eufi_benchmark.txt";
  system(("rm -rf " + file_name).c_str());

  for(unsigned i = 0; i < 1000; ++i){
    //OCTSignature S(ctx, 
    //num_constants, num_ineqs, max_limit);
    OCTSignature S(ctx, 10, 5, 3, 1000);
    if(!S.IsValidInstance()){
      --i;
      continue;
    }
    S.OCTIInstance();
    system(("echo \"test: " + S.MyName() + "\">> " + file_name).c_str());
    system(("{ time ./bin/eufi " + (OCTI_PREFIX + S.MyName()) + SMT_SUFFIX + "; } 2>> " + file_name).c_str());
    system(("rm " + (OCTI_PREFIX + S.MyName()) + SMT_SUFFIX).c_str());
  }
}
