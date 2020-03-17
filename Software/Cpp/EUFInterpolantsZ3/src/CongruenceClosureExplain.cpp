#include "CongruenceClosureExplain.h"
#define DEBUG_SANITY_CHECK 0
#define DEBUG_MERGE        0
#define DEBUG_PROPAGATE    0

CongruenceClosureExplain::CongruenceClosureExplain(const unsigned & min_id, const z3::expr_vector & subterms,
						   PredList & pred_list, UnionFindExplain & uf,
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
  uf                .resize(factory_curry_nodes.size());
  use_list          .resize(factory_curry_nodes.size());
  class_list_explain.resize(factory_curry_nodes.size());

#if 0
  for(auto x : factory_curry_nodes.hash_table)
    std::cout << *factory_curry_nodes.id_table[x.second->getId()] << std::endl;
#endif

  for(auto x : pending_explain)
    x.eq_cn.rhs->updateZ3Id(x.eq_cn.lhs->getZ3Id());
  
  while(!pending_explain.empty()){
    auto element = pending_explain.front();
    pending_explain.pop_front();
    merge(element);
  }
  
  for(auto x : ids_to_merge){
    auto const_id_lhs = factory_curry_nodes.curry_nodes[x.lhs_id]->getConstId(),
      const_id_rhs = factory_curry_nodes.curry_nodes[x.rhs_id]->getConstId();
    auto const_lhs = factory_curry_nodes.constantCurryNode(const_id_lhs),
      const_rhs = factory_curry_nodes.constantCurryNode(const_id_rhs);
    pending_explain.push_back(EquationCurryNodes(const_lhs, const_rhs));
  }
  
  while(!pending_explain.empty()){
    auto element = pending_explain.front();
    pending_explain.pop_front();
    merge(element);
  }

#if 1
  std::cout << uf << std::endl;
  // std::cout << factory_curry_nodes << std::endl;
#endif
}

CongruenceClosureExplain::~CongruenceClosureExplain(){
#if DEBUG_DESTRUCTORS_CC
  std::cout << "Done ~CongruenceClosureExplain" << std::endl;
#endif
}

void CongruenceClosureExplain::merge(const PendingElement & p){
  switch(p.tag){
  case EQ:{
#if DEBUG_MERGE
    auto s = p.eq_cn.lhs, t = p.eq_cn.rhs;
#endif
    switch(p.eq_cn.kind_equation){
    case CONST_EQ:
#if DEBUG_MERGE
      std::cout << "@merge. Merging constants" << std::endl
		<< *s << " and " << *t << std::endl;
#endif
      pending_explain.push_back(p.eq_cn);
      propagate();
      return;
    case APPLY_EQ:
#if DEBUG_MERGE
      std::cout << "@merge. Merging apply equations" << std::endl
		<< *s << " and " << *t << std::endl;
#endif
      auto repr_lhs = uf.find(p.eq_cn.lhs->getLeftId()),
	repr_rhs = uf.find(p.eq_cn.lhs->getRightId());
      try {
	// FIX: Problem with the 'element_found' being replaced by subsequent pointers
	EquationCurryNodes element_found = lookup_table.query(repr_lhs, repr_rhs);
#if DEBUG_MERGE
	std::cout << "@merge : element found "
		  << element_found << std::endl;
#endif
	std::cout << "BEGIN------" << std::endl;
	std::cout << p.eq_cn << " " << &(p.eq_cn) << std::endl;
	std::cout << "END------" << std::endl;
	
	pending_explain.push_back(PairEquationCurryNodes(&(p.eq_cn), &element_found));
        propagate();
      }
      catch(...){
	lookup_table.enter(repr_lhs, repr_rhs, p.eq_cn);
	use_list[repr_lhs].push_back(p.eq_cn);
	use_list[repr_rhs].push_back(p.eq_cn);
#if DEBUG_MERGE
	std::cout << "@merge: the element wasnt in the lookup table" << std::endl
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
  case EQ_EQ:
    throw "Problem @ CongruenceClosureExplain::merge(const PendingElement &).\
This method cannot take as input a PairEquation.";
  }
}

// KEEP: working here
void CongruenceClosureExplain::propagate(){
  while(!pending_explain.empty()) {
#if DEBUG_PROPAGATE
    std::cout << "@propagate. Taking this element " << pending_explain.front() << std::endl;
#endif

    CurryNode * a, * b;
    switch(pending_explain.front().tag){
    case EQ:
      a = pending_explain.front().eq_cn.lhs, b = pending_explain.front().eq_cn.rhs;
      break;
    case EQ_EQ:
      a = pending_explain.front().p_eq_cn.first->rhs, b = pending_explain.front().p_eq_cn.second->rhs;
      break;
    }
    
#if DEBUG_PROPAGATE
    std::cout << "@propagate. To merge these two inside uf: " << *b << " " << *a << std::endl;
#endif
    unsigned repr_a = uf.find(a->getId()), repr_b = uf.find(b->getId());

    if(repr_a != repr_b){
      // Invariant |ClassList(repr_a)| \leq |ClassList(repr_b)|
      if(class_list_explain[repr_a].size() > class_list_explain[repr_b].size()){
	std::swap(repr_a, repr_b);
	std::swap(a, b);
      }
      unsigned old_repr_a = repr_a;
      uf.merge(b->getId(), a->getId(), &pending_explain.front());
      
      auto last_pos_iterator = class_list_explain[repr_b].end();
      class_list_explain[repr_b].splice(last_pos_iterator, class_list_explain[old_repr_a]);
      // // Idk why the following crashes
      // class_list_explain[repr_b].splice(class_list_explain[repr_b].end(), class_list_explain[old_repr_a]);

      while(!use_list[old_repr_a].empty()) {
	unsigned c1 = use_list[old_repr_a].front().lhs->getLeftId(), c2 = use_list[old_repr_a].front().lhs->getRightId();
	unsigned repr_c1 = uf.find(c1), repr_c2 = uf.find(c2);
#if DEBUG_PROPAGATE	
	std::cout << "@propagate. Processing this equation: " << use_list[old_repr_a].front() << std::endl;
	std::cout << "@propagate. Constant arguments: " << c1 << " " << c2 << std::endl;
#endif
	try{
	  EquationCurryNodes * element_found = lookup_table.queryPointer(repr_c1, repr_c2);
	  std::cout << "New PairEqautionCurryNodes" << std::endl; // KEEP: working here
	  std::cout << *element_found << std::endl;
	  std::cout << use_list[old_repr_a].front() << std::endl;
#if DEBUG_PROPAGATE
	  std::cout << "@propagate. element found " << element_found << std::endl;
	  // // -----------------------------------------------------------------------
	  // std::cout << "BEGIN-------" << std::endl;
	  // std::cout << "Element found" << std::endl;
	  // std::cout << element_found << " " << *element_found << std::endl;
	  // std::cout << "Equation" << std::endl;
	  // std::cout << use_list[old_repr_a].front() << std::endl;
	  // std::cout << "END-------" << std::endl;
	  // // -----------------------------------------------------------------------
#endif	  
	  pending_explain.push_back(PairEquationCurryNodes(&use_list[old_repr_a].front(), element_found));
	}
	catch(...){
#if DEBUG_PROPAGATE
	  std::cout << "@propagate. the element wasnt in the lookup table" << std::endl;
#endif
	  lookup_table.enter(repr_c1, repr_c2, use_list[old_repr_a].front());
	  use_list[repr_b].push_back(use_list[old_repr_a].front());
	}
	use_list[old_repr_a].pop_front();
      }
    }
    pending_explain.pop_front();
  }
}

void CongruenceClosureExplain::buildCongruenceClosure(std::list<unsigned> & pending){
  throw "CongruenceClosureExplain::buildCongruenceClosure(std::list<unsigned> &). \
Implementation not defined";
}

std::ostream & operator << (std::ostream & os, const CongruenceClosureExplain & cc){
  return os;
}
