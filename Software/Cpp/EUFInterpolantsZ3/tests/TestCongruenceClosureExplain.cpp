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

std::ostream & operator << (std::ostream & os, TestCongruenceClosureExplain & test) {
  unsigned num_changes = 0;
  os << "All the original subterms:" << std::endl;

  for(auto it = test.subterms.begin(); it != test.subterms.end(); ++it){
    unsigned index = (*it).id();
    try {
      os << index << ". "
        << ((index == test.uf.find(index)) ? "(Same)" : "(Different)")
        << " Original: " << test.subterms[index]
        << " Representative position: " << test.uf.find(test.subterms[index].id())
        << " Representative " << test.subterms[test.uf.find(test.subterms[index].id())] // ISSUE: 
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

  return os;
}
