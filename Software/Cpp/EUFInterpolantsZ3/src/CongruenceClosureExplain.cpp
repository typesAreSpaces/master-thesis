#include "CongruenceClosureExplain.h"
#define DEBUG_SANITY_CHECK false

CongruenceClosureExplain::CongruenceClosureExplain(const unsigned & min_id, const z3::expr_vector & subterms,
						   CCList & pred_list, UnionFindExplain & uf,
						   const CurryDeclarations & curry_decl, FactoryCurryNodes & factory_curry_nodes) :
  CongruenceClosure(min_id, subterms, pred_list, uf), num_terms(subterms.size()),
  pending_explain(), lookup_table(uf), use_list(), class_list_explain(){
  
 
  factory_curry_nodes.curryfication(subterms[num_terms - 1]);
  factory_curry_nodes.flattening(pending_explain);

  // std::cout << factory_curry_nodes << std::endl;
  
  for(auto x : pending_explain)
    std::cout << x << std::endl;
    
  // KEEP: WORKING here. Update uf with the size of factory_curry_nodes
  // and update it using the merge that are pending!
  
  
}

CongruenceClosureExplain::~CongruenceClosureExplain(){
#if DEBUG_DESTRUCTORS_CC
  std::cout << "Done ~CongruenceClosureExplain" << std::endl;
#endif
}

void CongruenceClosureExplain::merge(CurryNode * s, CurryNode * t){
  if(s->isConstant() && t->isConstant()){
    pending_explain.push_back(EquationCurryNodes(s, t));
    propagate();
  }
  else{
    try {
      std::cout << "--------------" << std::endl;
      std::cout << *s << std::endl;
      std::cout << *t << std::endl;
      std::cout << "--------------" << std::endl;

      EquationCurryNodes whatever = lookup_table.query(0, 1);  // WRONG: Incomplete implementation
      
      std::cout << whatever << std::endl;
      pending_explain.push_back(EquationCurryNodes(s, t));
      propagate();
    }
    catch(...){
      lookup_table.enter(0, 1, EquationCurryNodes(nullptr, nullptr, APPLY_EQ)); // WRONG: Incomplete implementation
      // Update UseLists!!!
    }
  }
}

void CongruenceClosureExplain::propagate(){
  while(!pending_explain.empty()){
    auto eq = pending_explain.front();
    pending_explain.pop_front();

    switch(eq.kind_equation){
    case CONST_EQ:
      break;
    case APPLY_EQ:
      break;
    }

    
    
  }
}

void CongruenceClosureExplain::buildCongruenceClosure(std::list<unsigned> & pending){
  throw "CongruenceClosureExplain::buildCongruenceClosure(std::list<unsigned> &). Implementation not defined";
}

std::ostream & operator << (std::ostream & os, const CongruenceClosureExplain & cc){
  return os;

}
