#include "TestCongruenceClosureExplain.h"

TestCongruenceClosureExplain::TestCongruenceClosureExplain(z3::expr const & input_formula) :
  original_num_terms(input_formula.id() + 1),
  ctx(input_formula.ctx()), subterms(ctx), contradiction(ctx.bool_val(false)),
  fsym_positions(), uf(input_formula.id() + 1), pred_list(), 
  curry_decl(), factory_curry_nodes(original_num_terms, curry_decl)
{ 
  subterms .resize(original_num_terms);
  pred_list.resize(original_num_terms);
  init(input_formula);
  CongruenceClosureExplain cc(subterms, pred_list, uf, factory_curry_nodes);
}

void TestCongruenceClosureExplain::init(z3::expr const & e){
  if(e.is_app()){
    if(subterms.visited[e.id()])
      return;

    subterms.visited[e.id()] = true;
    subterms.set(e.id(), e);

    unsigned num = e.num_args();
    for(unsigned i = 0; i < num; i++)
      init(e.arg(i));

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
  throw "Problem @ EUFInterpolant::init. The expression e is not an application term.";
}

bool TestCongruenceClosureExplain::consistencyCheck(z3::expr const & e){

  z3::solver s(ctx);
  s.add(e);

  switch(s.check()){
    case z3::sat:
      std::cout << "This problem is sat" << std::endl;
      break;
    case z3::unsat:
      std::cout << "This problem is unsat" << std::endl;
      break;
    case z3::unknown:
      std::cout << "This problem is unknown" << std::endl;
      break;
  }

  return true;
}

void TestCongruenceClosureExplain::testExplanation(unsigned n){
  for(auto it = subterms.begin(); it != subterms.end(); ++it){
    unsigned index = (*it).id();
    if(index != uf.find(index)){
      n--;
      // TODO: Test explanation of nodes at index, uf.find(index)
      subterms[index];
      if(n == 0)
        return;
    }
  }
}

std::ostream & operator << (std::ostream & os, TestCongruenceClosureExplain & test) {
  unsigned num_changes = 0;
  os << "All the original subterms:" << std::endl;
  os << test.subterms.size() << std::endl;

  for(auto it = test.subterms.begin(); it != test.subterms.end(); ++it){
    unsigned index = (*it).id();
    try {
      unsigned repr_index = test.uf.find(test.subterms[index].id());
      os << index << ". "
        << ((index == test.uf.find(index)) ? "(Same)" : "(Different)")
        << " Original: " << test.subterms[index]
        << " Representative position: " << repr_index
        << " Representative " << test.subterms[repr_index] // ISSUE
        << " Representative " << test.factory_curry_nodes.getCurryNodeById(repr_index) // ISSUE
        << std::endl;
      if(index != test.uf.find(index))
        num_changes++;
    }
    catch(char const * e){
      os << e << std::endl;
      os << test.subterms[index].id() << std::endl;
      os << test.subterms.size() << std::endl;
      os << test.uf.find(test.subterms[index].id()) << std::endl;
    }
  }

  std::cout << "Number of changes: " << num_changes << std::endl;

  return os;
}
