#include "TestCongruenceClosureExplain.h"
#include <z3++.h>

TestCongruenceClosureExplain::TestCongruenceClosureExplain(z3::expr_vector const & assertions) :

  original_num_terms(maxIdFromAssertions(assertions) + 1),
  ctx(assertions.ctx()), subterms(ctx), contradiction(ctx.bool_val(false)),
  fsym_positions(), uf(original_num_terms), pred_list(), 
  curry_decl(), factory_curry_nodes(original_num_terms, curry_decl),
  cc(
      (
       subterms.resize(original_num_terms), 
       pred_list.resize(original_num_terms), 
       init(assertions), 
       subterms), pred_list, uf, factory_curry_nodes, ids_to_merge
      )
{ 
}

unsigned TestCongruenceClosureExplain::maxIdFromAssertions(z3::expr_vector const & assertions){
  unsigned max_id_from_assertions = 0;
  for(auto const & assertion : assertions){
    if(assertion.id() > max_id_from_assertions)
      max_id_from_assertions = assertion.id();
  }
  return max_id_from_assertions;
}

void TestCongruenceClosureExplain::init(z3::expr_vector const & assertions){
  for(auto const & assertion : assertions){
    initFormula(assertion);
    switch(assertion.decl().decl_kind()){
      case Z3_OP_EQ:
        ids_to_merge.emplace_back(assertion.arg(0).id(), assertion.arg(1).id());
        break;
      default:
        break;
    }
  }
  return;
}

void TestCongruenceClosureExplain::initFormula(z3::expr const & e){
  if(e.is_app()){
    if(subterms.visited[e.id()])
      return;

    subterms.visited[e.id()] = true;
    subterms.set(e.id(), e);

    unsigned num = e.num_args();
    for(unsigned i = 0; i < num; i++)
      initFormula(e.arg(i));

    z3::func_decl f = e.decl();
    if(curry_decl[f.id()] == nullptr)
      curry_decl[f.id()] = factory_curry_nodes.newCurryNode(e.id(), f.name().str(), nullptr, nullptr);

    switch(f.decl_kind()){
      case Z3_OP_UNINTERPRETED:
        if(num > 0)
          fsym_positions[f.name().str()].push_back(e.id());
      default:
        return;
    }
  }
  throw "Problem @ EUFInterpolant::initFormula. The expression e is not an application term.";
}

bool TestCongruenceClosureExplain::testConsistency(z3::expr_vector const & e, 
    unsigned max_iter){
  z3::solver s(ctx);
  for(auto const & assertion : e)
    s.add(assertion);

  std::cout << "Starting consistency test" << std::endl;

  for(auto it = subterms.begin();  it != subterms.end(); ++it){
    unsigned index = (*it).id();
    auto repr = cc.z3_repr(index);
    unsigned repr_index = repr.id();
    // Checking the non-trivial equalities
    // of the same sort
    if(index != repr_index 
        && (*it).get_sort().id() == repr.get_sort().id()){
      s.push();
      std::cout << "To check that " 
        << *it << " and " << repr 
        << " are equivalent: ";
      s.add((*it) != repr);
      switch(s.check()){
        case z3::unsat:
          std::cout << "They are." << std::endl;
          break;
        default:
          throw "There is a problem with the congruence closure algorithm";
      }
      s.pop();
      if(--max_iter == 0)
        return true;
    }
  }
  return true;
}

void TestCongruenceClosureExplain::testExplanation(unsigned max_iter){
  for(auto it = subterms.begin(); it != subterms.end(); ++it){
    unsigned index = (*it).id();
    auto repr = cc.z3_repr(index);
    unsigned repr_index = repr.id();
    // Checking the non-trivial equalities
    if(index != repr_index){
      cc.giveZ3Explanation(std::cout, *it, repr);
      if(--max_iter == 0)
        return;
    }
  }
  return;
}

std::ostream & operator << (std::ostream & os, TestCongruenceClosureExplain & test) {
  unsigned num_changes = 0;
  os << "Printing all the original subterms:" << std::endl;
  os << test.subterms.size() << std::endl;

  for(auto it = test.subterms.begin(); it != test.subterms.end(); ++it){
    unsigned index = (*it).id();
    try {
      assert(test.subterms[index].id() == index);
      
      auto repr = test.cc.z3_repr(index);
      unsigned repr_index = repr.id();

      os << index << ". " << (index == repr_index ? "(Same)" : (num_changes++, "(Different)")) << std::endl;
      os << "Original:       " << test.subterms[index] << std::endl;
      os << "Representative: " << repr << std::endl;

    }
    catch(char const * e){
      os << e << std::endl;
      os << index << std::endl;
    }
  }

  os << "Number of changes: " << num_changes;

  return os;
}
