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

  //os << "Printing UF Explanation" << std::endl;
  //// Currently this is the *only* way to see actual partitions 
  //// produced by the Congruence Closure algorithm 
  //os << test.uf << std::endl;

  //os << "Printing node factory" << std::endl;
  //os << test.factory_curry_nodes;

  unsigned num_changes = 0;
  os << "Printing all the original subterms:" << std::endl;
  os << test.subterms.size() << std::endl;

  for(auto it = test.subterms.begin(); it != test.subterms.end(); ++it){
    unsigned index = (*it).id();
    try {
      assert(test.subterms[index].id() == index);

      // KEEP: working here
      // Find a scheme to show the representative 
      // element for each subterm using id, z3_id, const_id, etc
      
      CurryNode * term = test.factory_curry_nodes.getCurryNodeById(index);
      unsigned const_id = term->getConstId(); 
      unsigned repr_const_id = test.uf.find(const_id);
      CurryNode * repr_term = test.factory_curry_nodes.getCurryNodeById(repr_const_id);
      unsigned repr_index = repr_term->getZ3Id();

      os << index << ". "
        << ((index == repr_index) ? "(Same)" : "(Different)")
        << " Original: " << test.subterms[index]
        << " Representative position: " << repr_index
        << " Representative " << test.subterms[repr_index] // ISSUE
        << std::endl;

      os << *term << std::endl;
      //os << *repr_term << std::endl;

      if(index != repr_index)
        num_changes++;
    }
    catch(char const * e){
      os << e << std::endl;
      os << index << std::endl;
    }
  }

  std::cout << "Number of changes: " << num_changes << std::endl;

  return os;
}
