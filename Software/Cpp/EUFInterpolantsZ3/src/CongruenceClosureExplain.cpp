#include "CongruenceClosureExplain.h"
#define DEBUG_SANITY_CHECK false
#define DEBUG_MERGE        false

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
  // in the curry_nodes and extra_nodes. There
  // might be repeated elements in these collection
  // but they are unique pointers
  uf.increaseSize(factory_curry_nodes.size());
  use_list.resize(factory_curry_nodes.size());

#if 0
  for(auto x : factory_curry_nodes.hash_table)
    std::cout << *factory_curry_nodes.id_table[x.second->getId()] << std::endl;
#endif

#if DEBUG_MERGE
  std::cout << "----Pending explain" << std::endl;
#endif
  for(auto x : pending_explain){
#if DEBUG_MERGE
    std::cout << "------------------------------------" << std::endl;
#endif
    merge(x);
  }
  
  // Elements from the lookup_table
  // std::cout << lookup_table << std::endl;

#if 0
  std::cout << "----Ids to merge" << std::endl;
  for(auto x : ids_to_merge)
    std::cout << *factory_curry_nodes.curry_nodes[x.lhs_id]
	      << " = "
	      << *factory_curry_nodes.curry_nodes[x.rhs_id]
	      << std::endl;
#endif
}

CongruenceClosureExplain::~CongruenceClosureExplain(){
#if DEBUG_DESTRUCTORS_CC
  std::cout << "Done ~CongruenceClosureExplain" << std::endl;
#endif
}

void CongruenceClosureExplain::merge(const PendingElement & p){
  switch(p.tag){
  case Equation:{
#if DEBUG_MERGE
    auto s = p.eq_cn.lhs, t = p.eq_cn.rhs;
#endif
    switch(p.eq_cn.kind_equation){
    case CONST_EQ:
#if DEBUG_MERGE
      std::cout << "Merging constants" << std::endl
		<< *s << " = " << *t << std::endl;
#endif
      pending_explain.push_back(p.eq_cn);
      propagate();
      return;
    case APPLY_EQ:
#if DEBUG_MERGE
      std::cout << "Merging apply equations" << std::endl
		<< *s << " = " << *t << std::endl;
#endif
      auto repr_lhs = uf.find(p.eq_cn.lhs->getLeftId()),
	repr_rhs = uf.find(p.eq_cn.lhs->getRightId());
      try {	 
	EquationCurryNodes element_found = lookup_table.\
	  query(repr_lhs, repr_rhs);
#if DEBUG_MERGE
	std::cout << "Element found "
		  << element_found << std::endl;
#endif
	pending_explain.\
	  push_back(PairEquationCurryNodes(p.eq_cn, element_found));
        propagate();
      }
      catch(...){
	lookup_table.enter(repr_lhs, repr_rhs, p.eq_cn);
	use_list[repr_lhs].push_back(p.eq_cn);
	use_list[repr_rhs].push_back(p.eq_cn);
#if DEBUG_MERGE
	std::cout << "Element wasnt in the lookup table" << std::endl
		  << "------------------------------------------"
		  << std::endl
		  << "Index lhs " << p.eq_cn.lhs->getLeftId()
		  << "[" << repr_lhs << "] has this in UseList "
		  << p.eq_cn << std::endl
		  << "Index rhs " << p.eq_cn.lhs->getRightId()
		  << "[" << repr_rhs << "] has this in UseList "
		  << p.eq_cn << std::endl
		  << "------------------------------------------"
		  << std::endl;
#endif
      }
      return;
    }
  }
  case PairEquation:
    throw "Problem @ CongruenceClosureExplain::merge(const PendingElement &).\
This method cannot take as input a PairEquation.";
  }
}

// KEEP: working here
void CongruenceClosureExplain::propagate(){
  std::cout << "Keep working @ CongruenceClosureExplain::propagate()." << std::endl;
#if 0
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
#endif
}

void CongruenceClosureExplain::buildCongruenceClosure(std::list<unsigned> & pending){
  throw "CongruenceClosureExplain::buildCongruenceClosure(std::list<unsigned> &). Implementation not defined";
}

std::ostream & operator << (std::ostream & os, const CongruenceClosureExplain & cc){
  return os;

}
