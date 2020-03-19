#include "CongruenceClosureExplain.h"
#include <fstream>
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

  merge();

  // Process input-equation defined by user
  for(auto x : ids_to_merge){
    auto const_id_lhs = factory_curry_nodes.curry_nodes[x.lhs_id]->getConstId(),
      const_id_rhs = factory_curry_nodes.curry_nodes[x.rhs_id]->getConstId();
    auto const_lhs = factory_curry_nodes.constantCurryNode(const_id_lhs),
      const_rhs = factory_curry_nodes.constantCurryNode(const_id_rhs);
    pending_propagate.push_back(EquationCurryNodes(const_lhs, const_rhs));
  }
 
  propagate();

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

void CongruenceClosureExplain::merge(){
  while(!equations_to_merge.empty()) {    
    const auto & equation_to_merge = equations_to_merge.back();
    switch(equation_to_merge.tag) {
    case EQ: {
#if DEBUG_MERGE
      auto s = equation_to_merge.eq_cn.lhs, t = equation_to_merge.eq_cn.rhs;
#endif
      switch(equation_to_merge.eq_cn.kind_equation) {
      case CONST_EQ:
#if DEBUG_MERGE
	std::cout << "@merge. Merging constants" << std::endl
		  << *s << " and " << *t << std::endl;
#endif
	pending_propagate.push_back(equation_to_merge.eq_cn);
	propagate();
	break;
      case APPLY_EQ: {
#if DEBUG_MERGE
	std::cout << "@merge. Merging apply equations" << std::endl
		  << *s << " and " << *t << std::endl;
#endif
	auto repr_lhs = uf.find(equation_to_merge.eq_cn.lhs->getLeftId()),
	  repr_rhs = uf.find(equation_to_merge.eq_cn.lhs->getRightId());

	const EquationCurryNodes * element_found = lookup_table.query(repr_lhs, repr_rhs);

	if(element_found != nullptr){
#if DEBUG_MERGE
	  std::cout << "@merge : element found "
		    << element_found << std::endl;
	  std::cout << equation_to_merge.eq_cn << " " << &(equation_to_merge.eq_cn) << std::endl;
#endif
	  pending_propagate.push_back(PairEquationCurryNodes(&(equation_to_merge.eq_cn), element_found));
	  propagate();
	}
	else{
	  lookup_table.enter(repr_lhs, repr_rhs, &(equation_to_merge.eq_cn));
	  use_list[repr_lhs].push_back(equation_to_merge.eq_cn);
	  use_list[repr_rhs].push_back(equation_to_merge.eq_cn);
#if DEBUG_MERGE
	  std::cout << "@merge: the element wasnt in the lookup table" << std::endl
		    << "------------------------------------------"
		    << std::endl
		    << "Index lhs " << equation_to_merge.eq_cn.lhs->getLeftId()
		    << "[repr:" << repr_lhs << "] has this in UseList "
		    << equation_to_merge.eq_cn << std::endl
		    << "Index rhs " << equation_to_merge.eq_cn.lhs->getRightId()
		    << "[repr:" << repr_rhs << "] has this in UseList "
		    << equation_to_merge.eq_cn << std::endl
		    << &equation_to_merge.eq_cn << std::endl
		    << "------------------------------------------"
		    << std::endl;
#endif
	}
	break;
      }
      }
      equations_to_merge.pop_back();
      break;
    }
    case EQ_EQ:
      throw "Problem @ CongruenceClosureExplain::merge(). \
This method cannot take as input a PairEquation.";
    }
  }
}

void CongruenceClosureExplain::propagate(){
  while(!pending_propagate.empty()) {
    const auto & pending_element = pending_propagate.back();
    pending_propagate.pop_back();
#if DEBUG_PROPAGATE
    std::cout << "@propagate. Taking this element " << pending_element << std::endl;
#endif
    CurryNode * a, * b;
    switch(pending_element.tag){
    case EQ:
      a = pending_element.eq_cn.lhs, b = pending_element.eq_cn.rhs;
      break;
    case EQ_EQ:
      a = pending_element.p_eq_cn.first->rhs, b = pending_element.p_eq_cn.second->rhs;
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
      const auto & wow = &(pending_element);
      uf.merge(b->getId(), a->getId(), wow);
      class_list_explain[repr_b].splice(class_list_explain[repr_b].end(), class_list_explain[old_repr_a]);

      while(!use_list[old_repr_a].empty()) {
	const auto & equation = use_list[old_repr_a].back();
	use_list[old_repr_a].pop_back();	
	unsigned c1 = equation.lhs->getLeftId(), c2 = equation.lhs->getRightId();
	unsigned repr_c1 = uf.find(c1), repr_c2 = uf.find(c2);
#if DEBUG_PROPAGATE
	std::cout << "@propagate. Processing this equation: " << equation << " " << std::endl;
	std::cout << "@propagate. Constant arguments: " << c1 << " " << c2 << std::endl;
#endif
	const EquationCurryNodes * element_found = lookup_table.query(repr_c1, repr_c2);

	if(element_found != nullptr){
#if DEBUG_PROPAGATE
	  // --------------------------------------------------------------------------
	  std::cout << "New PairEquationCurryNodes" << std::endl; // KEEP: working here
	  std::cout << "1. ----------------------- " << element_found << std::endl;
	  std::cout << "2. ----------------------- " << equation << std::endl;
	  // std::cout << new_entry << std::endl;
	  // --------------------------------------------------------------------------
#endif
	  pending_propagate.push_back(PairEquationCurryNodes(&equation, element_found));
	}
	else{
#if DEBUG_PROPAGATE
	  std::cout << "@propagate. the element wasnt in the lookup table" << std::endl;
#endif
	  use_list[repr_b].push_back(equation);
	  lookup_table.enter(repr_c1, repr_c2, &equation);
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
