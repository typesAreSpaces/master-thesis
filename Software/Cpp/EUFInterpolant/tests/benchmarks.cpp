#include <iostream>
#include <z3++.h>
#include <set>
#include <vector>
#include <list>
#include <stdio.h>
#include <stdlib.h>
#include <time.h> 
#define DEBUG 0

class EUFSignature {

  z3::context & ctx;
  z3::expr_vector constants;
  z3::func_decl_vector func_names;

  z3::expr_vector grounded_terms;
  std::set<unsigned> ids;
  z3::expr_vector a_part;
  z3::expr_vector b_part;

  z3::sort_vector k_ary_sort(z3::sort const &, unsigned);
  std::list<z3::expr_vector> allCandidates(unsigned);
  std::vector<z3::expr_vector> cartesianProd(
      std::list<z3::expr_vector>);

  void build_ground_terms(unsigned);
  void build_a_part(unsigned, unsigned);
  void build_b_part(z3::solver &, unsigned, unsigned);

  public:
  EUFSignature(z3::context &, z3::sort const &,
      unsigned, unsigned, 
      unsigned, unsigned, 
      unsigned, unsigned);

  friend std::ostream & operator << (std::ostream &, EUFSignature const &);
};

int main(){
  /* initialize random seed: */
  srand(time(NULL));

  z3::context ctx;
  z3::sort sort_A = ctx.uninterpreted_sort("A");

  EUFSignature S(ctx, sort_A,
      10,    // num_constants
      5,     // num_func_names
      3,     // max_arity
      10,    // max_num_a_lists
      100,   // max_ground_position
      1000); // limit_search

  //std::cout << S << std::endl;

  return 0;
}

z3::sort_vector EUFSignature::k_ary_sort(z3::sort const & s, unsigned n){
  z3::sort_vector ans(ctx);
  for(unsigned i = 0; i < n; ++i)
    ans.push_back(s);
  return ans;
}

std::list<z3::expr_vector > EUFSignature::allCandidates(unsigned arity){
  std::list<z3::expr_vector > ans({});

  for(unsigned index = 0; index < arity; index++)
    ans.push_back(grounded_terms);

  return ans;
}

std::vector<z3::expr_vector> EUFSignature::cartesianProd(std::list<z3::expr_vector> candidates){
  // ans_size can get really large
  // at most O(n^n)
  // so be aware of 
  // overflow problems
  unsigned ans_size = 1;
  for(auto const & entry : candidates)
    ans_size *= entry.size();

  std::vector<z3::expr_vector> ans;
  ans.reserve(ans_size);
  for(unsigned i = 0; i < ans_size; ++i)
    ans.push_back(z3::expr_vector(ctx));

  if(ans_size){
    unsigned max_repetition = 1;
    for(auto const & entry : candidates){
      unsigned index = 0;
      while(index < ans_size)
        for(auto const & value : entry){
          unsigned index_repetition = 0;
          while(index_repetition++ < max_repetition)
            ans[index++].push_back(value);
        }
      max_repetition *= entry.size();
    }
  }

  return ans;
}

void EUFSignature::build_ground_terms(unsigned max_ground_position){
  for(auto const & constant : constants)
    grounded_terms.push_back(constant);
  while(true){
    for(auto const & f_name : func_names){
      unsigned current_arity = f_name.arity();
      auto const & lol = cartesianProd(allCandidates(current_arity));
      for(auto const & input : lol){
        grounded_terms.push_back(f_name(input));
        if(grounded_terms.size() >= max_ground_position)
          return;
      }
    }
  }
}

void EUFSignature::build_a_part(unsigned max_num_a_lits, unsigned max_ground_position){
  unsigned counter_a_part = 0;
  while(counter_a_part < max_num_a_lits){
    unsigned pos_1 = rand() % max_ground_position;
    unsigned pos_2 = rand() % max_ground_position;
    auto const & term_1 = grounded_terms[pos_1];
    auto const & term_2 = grounded_terms[pos_2];
    auto const & new_eq_or_diseq = 
      (rand() % 2 == 1) ? 
      term_1 == term_2 : 
      term_1 != term_2 ;
    if(term_1.id() != term_2.id() 
        && ids.find(new_eq_or_diseq.id()) == ids.end()){
      ids.insert(new_eq_or_diseq.id());
      a_part.push_back(new_eq_or_diseq);
      ++counter_a_part;
    }
  }
}

void EUFSignature::build_b_part(z3::solver & sol, 
    unsigned max_ground_position, unsigned limit_search){
  auto current_check = sol.check();

  unsigned num_iter = 0;

  while(current_check != z3::unsat){
    unsigned pos_1 = rand() % max_ground_position;
    unsigned pos_2 = rand() % max_ground_position;
    auto const & term_1 = grounded_terms[pos_1];
    auto const & term_2 = grounded_terms[pos_2];
    auto const & new_eq_or_diseq = 
      (rand() % 2 == 1) ? 
      term_1 == term_2 : 
      term_1 != term_2 ;
    if(term_1.id() != term_2.id() 
        && ids.find(new_eq_or_diseq.id()) == ids.end()){
      ids.insert(new_eq_or_diseq.id());
      b_part.push_back(new_eq_or_diseq);
      sol.add(new_eq_or_diseq);
    }
    current_check = sol.check();
    if(num_iter > limit_search)
      return;
  }
}

EUFSignature::EUFSignature(z3::context & ctx, z3::sort const & sort_A,
    unsigned num_constants, unsigned num_func_names, 
    unsigned max_arity, unsigned max_num_a_lits, 
    unsigned max_ground_position, unsigned limit_search) : 
  ctx(ctx), constants(ctx), func_names(ctx),
  grounded_terms(ctx), 
  ids({}), a_part(ctx), b_part(ctx)
{
  for(unsigned i = 0; i < num_constants; ++i)
    constants.push_back(ctx.constant(
          ("x_" + std::to_string(i)).c_str(), sort_A));
  for(unsigned i = 0; i < num_func_names; ++i)
    func_names.push_back(ctx.function(
          ("f_" + std::to_string(i)).c_str(), 
          k_ary_sort(sort_A, rand() % max_arity + 1), sort_A));

  build_ground_terms(max_ground_position);
  build_a_part(max_num_a_lits, max_ground_position);

  z3::solver sol(ctx);
  for(auto const & eq : a_part)
    sol.add(eq);
  if(sol.check() == z3::sat){
#if DEBUG
    std::cout << "Valid instance" << std::endl;
#endif
    build_b_part(sol, max_ground_position, limit_search);
  }
#if DEBUG
  else
    std::cout << "Not valid instance" << std::endl;
#endif
  std::cout << sol.to_smt2() << std::endl;
}

std::ostream & operator << (std::ostream & os, EUFSignature const & eufs){
  os << "A part formulas:" << std::endl;
  os << eufs.a_part << std::endl;
  os << "B part formulas:" << std::endl;
  os << eufs.b_part << std::endl;
  return os;
}
