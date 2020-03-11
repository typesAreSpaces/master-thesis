#include "CongruenceClosureExplain.h"
#define DEBUG_SANITY_CHECK false

CongruenceClosureExplain::CongruenceClosureExplain(const unsigned & min_id, const z3::expr_vector & subterms,
						   CCList & pred_list, UnionFindExplain & uf,
						   const CurryDeclarations & curry_decl, FactoryCurryNodes & factory_curry_nodes) :
  CongruenceClosure(min_id, subterms, pred_list, uf), num_terms(subterms.size()),
  pending_explain(), lookup_table(uf), use_list(), class_list_explain(){
  
 
  auto ids_to_merge = factory_curry_nodes.curryfication(subterms[num_terms - 1]);
  // NOTE: The new constants
  // introduced by flattening
  // are in extra_nodes
  factory_curry_nodes.flattening(min_id, pending_explain);

  // There is an element in uf for each element
  // in the hash_table of factory_curry_nodes
  uf.increaseSize(factory_curry_nodes.size());

#if 0
  for(auto x : factory_curry_nodes.hash_table)
    std::cout << *factory_curry_nodes.id_table[x.second->getId()] << std::endl;
#endif

#if 1
  std::cout << "----Pending explain" << std::endl;
  for(auto x : pending_explain)
    merge(x.lhs, x.rhs);
#endif
  
#if 0
  std::cout << "----Ids to merge" << std::endl;
  for(auto x : ids_to_merge)
    std::cout << *factory_curry_nodes.curry_nodes[x.lhs_id]
	      << " = "
	      << *factory_curry_nodes.curry_nodes[x.rhs_id]
	      << std::endl;
#endif
  
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
    std::cout << "Merging constants" << std::endl;
    // pending_explain.push_back(EquationCurryNodes(s, t));
    // propagate();
  }
  else{
    std::cout << "Merging apply equations" << std::endl;
    try {
      EquationCurryNodes whatever = lookup_table.query(0, 1);  // WRONG: Incomplete implementation
      
      // std::cout << whatever << std::endl;
      // pending_explain.push_back(EquationCurryNodes(s, t));
      // propagate();
    }
    catch(...){
      std::cout << "Haha, the element wasnt in the lookup table" << std::endl;
      // lookup_table.enter(0, 1, EquationCurryNodes(nullptr, nullptr, APPLY_EQ)); // WRONG: Incomplete implementation
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
