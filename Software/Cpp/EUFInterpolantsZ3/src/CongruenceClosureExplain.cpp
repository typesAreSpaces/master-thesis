#include "CongruenceClosureExplain.h"
#define DEBUG_SANITY_CHECK 0
#define DEBUG_MERGE        0
#define DEBUG_PROPAGATE    0

CongruenceClosureExplain::CongruenceClosureExplain(const unsigned & min_id, const z3::expr_vector & subterms,
						   PredList & pred_list, UnionFindExplain & uf,
						   const CurryDeclarations & curry_decl, FactoryCurryNodes & factory_curry_nodes) :
  CongruenceClosure(min_id, subterms, pred_list, uf), num_terms(subterms.size()),
  equations_to_merge(), pending_propagate(), lookup_table(), use_list(), class_list_explain(){
  
 
  auto ids_to_merge = factory_curry_nodes.curryfication(subterms[num_terms - 1]);
  
  // NOTE: The new constants
  // introduced by flattening
  // are in extra_nodes
  factory_curry_nodes.flattening(min_id, equations_to_merge);
  
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

  for(auto x : equations_to_merge)
    x.eq_cn.rhs->updateZ3Id(x.eq_cn.lhs->getZ3Id());

  while(!equations_to_merge.empty()){
    auto element = equations_to_merge.back();
    equations_to_merge.pop_back();
    merge(element);
  }

  // Process input-equation defined by user
  for(auto x : ids_to_merge){
    auto const_id_lhs = factory_curry_nodes.curry_nodes[x.lhs_id]->getConstId(),
      const_id_rhs = factory_curry_nodes.curry_nodes[x.rhs_id]->getConstId();
    auto const_lhs = factory_curry_nodes.constantCurryNode(const_id_lhs),
      const_rhs = factory_curry_nodes.constantCurryNode(const_id_rhs);
    pending_propagate.push_back(EquationCurryNodes(const_lhs, const_rhs));
  }
  
  propagate();

#if 0
  std::cout << uf << std::endl;
  // std::cout << factory_curry_nodes << std::endl;
#endif
}

CongruenceClosureExplain::~CongruenceClosureExplain(){
#if DEBUG_DESTRUCTORS_CC
  std::cout << "Done ~CongruenceClosureExplain" << std::endl;
#endif
}

void CongruenceClosureExplain::merge(const PendingElement & p) {
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
      pending_propagate.push_back(p.eq_cn);
      propagate();
      break;
    case APPLY_EQ:
#if DEBUG_MERGE
      std::cout << "@merge. Merging apply equations" << std::endl
		<< *s << " and " << *t << std::endl;
#endif
      auto repr_lhs = uf.find(p.eq_cn.lhs->getLeftId()),
	repr_rhs = uf.find(p.eq_cn.lhs->getRightId());

      const EquationCurryNodes * element_found = lookup_table.query(repr_lhs, repr_rhs);

      if(element_found == nullptr){
	lookup_table.enter(repr_lhs, repr_rhs, p.addressEquationCurryNodes());
	// std::cout << "mmm " << &p.eq_cn << std::endl;
	std::cout << "mmm " << p.addressEquationCurryNodes() << std::endl;
	use_list[repr_lhs].push_back(p.eq_cn);
	use_list[repr_rhs].push_back(p.eq_cn);
#if DEBUG_MERGE
	std::cout << "@merge: the element wasnt in the lookup table" << std::endl
		  << "------------------------------------------"
		  << std::endl
		  << "Index lhs " << p.eq_cn.lhs->getLeftId()
		  << "[repr:" << repr_lhs << "] has this in UseList "
		  << p.eq_cn << std::endl
		  << "Index rhs " << p.eq_cn.lhs->getRightId()
		  << "[repr:" << repr_rhs << "] has this in UseList "
		  << p.eq_cn << std::endl
		  << &p.eq_cn << std::endl
		  << "------------------------------------------"
		  << std::endl;
#endif
      }
      else{
	// FIX: Problem with the 'element_found' being replaced by subsequent pointers

#if DEBUG_MERGE
	std::cout << "@merge : element found "
		  << element_found << std::endl;
#endif
	std::cout << "(this needs to be fixed, perhaps not)BEGIN------" << std::endl;
	std::cout << p.eq_cn << " " << &(p.eq_cn) << std::endl;
	std::cout << "END------" << std::endl;
	
	pending_propagate.push_back(PairEquationCurryNodes(&(p.eq_cn), element_found));
        propagate();
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
  while(!pending_propagate.empty()) {

    auto pending_element = &pending_propagate.back();
    pending_propagate.pop_back();
    
#if DEBUG_PROPAGATE
    std::cout << "@propagate. Taking this element " << pending_element << " " << *pending_element << std::endl;
#endif

    CurryNode * a, * b;
    switch(pending_element->tag){
    case EQ:
      a = pending_element->eq_cn.lhs, b = pending_element->eq_cn.rhs;
      break;
    case EQ_EQ:
      a = pending_element->p_eq_cn.first->rhs, b = pending_element->p_eq_cn.second->rhs;
      break;
    }
    
#if DEBUG_PROPAGATE
    std::cout << "@propagate. To merge these two inside uf: " << *b << " " << *a << std::endl;
#endif
    unsigned repr_a = uf.find(a->getId()), repr_b = uf.find(b->getId());

    if(repr_a != repr_b) {
      // Invariant |ClassList(repr_a)| \leq |ClassList(repr_b)|
      if(class_list_explain[repr_a].size() > class_list_explain[repr_b].size()){
	std::swap(repr_a, repr_b);
	std::swap(a, b);
      }
      unsigned old_repr_a = repr_a;
      uf.merge(b->getId(), a->getId(), pending_element);
      
      // auto last_pos_iterator = class_list_explain[repr_b].end();
      // class_list_explain[repr_b].splice(last_pos_iterator, class_list_explain[old_repr_a]);
      // Idk why the following crashes -- Checking
      class_list_explain[repr_b].splice(class_list_explain[repr_b].end(), class_list_explain[old_repr_a]);

      while(!use_list[old_repr_a].empty()) {
	auto equation = &use_list[old_repr_a].back();
	use_list[old_repr_a].pop_back();
	
	unsigned c1 = equation->lhs->getLeftId(), c2 = equation->lhs->getRightId();
	unsigned repr_c1 = uf.find(c1), repr_c2 = uf.find(c2);
	
#if DEBUG_PROPAGATE	
	std::cout << "@propagate. Processing this equation: " << equation << " " << *equation << std::endl;
	std::cout << "@propagate. Constant arguments: " << c1 << " " << c2 << std::endl;
#endif
	const EquationCurryNodes * element_found = lookup_table.query(repr_c1, repr_c2);

	if(element_found == nullptr){	  	  
#if DEBUG_PROPAGATE
	  std::cout << "@propagate. the element wasnt in the lookup table" << std::endl;
#endif
	  use_list[repr_b].push_back(*equation);
	  
	  // UseList a;
	  // a.resize(1);
	  // a[0].push_back(*equation);
	  // a[0].pop_back();
	  
	  lookup_table.enter(repr_c1, repr_c2, equation);
	}
	else{
	  auto new_entry = PairEquationCurryNodes(equation, element_found);
	  #if DEBUG_PROPAGATE	
	  // --------------------------------------------------------------------------
	  std::cout << "New PairEquationCurryNodes" << std::endl; // KEEP: working here
	  std::cout << "1. ----------------------- " << element_found << " " << *element_found << std::endl;
	  std::cout << "2. ----------------------- " << equation << " " << *equation << std::endl;
	  std::cout << new_entry << std::endl;
	  // --------------------------------------------------------------------------
#endif
	  pending_propagate.push_back(new_entry);
	}
	
      }
      
    }
  }
}

void CongruenceClosureExplain::buildCongruenceClosure(std::list<unsigned> & pending){
  throw "CongruenceClosureExplain::buildCongruenceClosure(std::list<unsigned> &). \
Implementation not defined";
}

std::ostream & operator << (std::ostream & os, const CongruenceClosureExplain & cc){
  return os;
}
