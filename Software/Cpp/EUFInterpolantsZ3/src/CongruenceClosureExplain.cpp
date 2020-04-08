#include "CongruenceClosureExplain.h"

#define DEBUG_SANITY_CHECK  1
#define DEBUG_MERGE         0
#define DEBUG_PROPAGATE     1
#define DEBUG_PROPAGATE_AUX 0

CongruenceClosureExplain::CongruenceClosureExplain(const unsigned & min_id, const z3::expr_vector & subterms,
    PredList & pred_list, UnionFindExplain & uf,
    FactoryCurryNodes & factory_curry_nodes) :
  CongruenceClosure(min_id, subterms, pred_list, uf), 
  num_terms(subterms.size()), subterms(subterms), factory_curry_nodes(factory_curry_nodes), ufe(uf),
  pending_elements(), equations_to_merge(), pending_to_propagate(),
  lookup_table(), use_list() 
{

  auto ids_to_merge = factory_curry_nodes.curryfication(subterms[num_terms - 1]);

  // NOTE: The new constants introduced by flattening are in extra_nodes
  // NOTE2: flattening also fully defines const_id and z3_id for each curry node.
  factory_curry_nodes.flattening(min_id, pending_elements, equations_to_merge, subterms);

  // Process input-equations defined by user
  // using the constant ids
  for(auto x : ids_to_merge){
    auto const_lhs = factory_curry_nodes.constantZ3Index(x.lhs_id),
         const_rhs = factory_curry_nodes.constantZ3Index(x.rhs_id);
    pushPending(pending_to_propagate, EquationCurryNodes(*const_lhs, *const_rhs));
  }

  // There is an element in uf for each element
  // in the curry_nodes and extra_nodes. There
  // might be repeated elements in these collection
  // but they are unique pointers
  ufe     .resize(factory_curry_nodes.size());
  use_list.resize(factory_curry_nodes.size());

#if 0
  // This code exemplifies how to retrieve back an original id
  for(auto x : factory_curry_nodes.hash_table)
    std::cout << *factory_curry_nodes.id_table[x.second->getId()] << std::endl;
#endif

  merge();
  propagate();

#if DEBUG_SANITY_CHECK
  //std::cout << uf << std::endl;
  //std::cout << factory_curry_nodes << std::endl;
#endif
}

CongruenceClosureExplain::~CongruenceClosureExplain(){
#if DEBUG_DESTRUCTORS_CC
  std::cout << "Done ~CongruenceClosureExplain" << std::endl;
#endif
}

void CongruenceClosureExplain::pushPending(PendingElementsPointers & pending_pointers, 
    const PendingElement & pe){
  pending_elements.push_back(pe);
  pending_pointers.push_back(&pending_elements.back());
}

EqClass CongruenceClosureExplain::highestNode(EqClass a, UnionFind & uf){
  return uf.find(a);
}

EqClass CongruenceClosureExplain::nearestCommonAncestor(EqClass a, EqClass b, UnionFind & uf){
  return uf.find(ufe.commonAncestor(a, b));
}

void CongruenceClosureExplain::merge(const EquationCurryNodes & equation){
  const auto & lhs = equation.lhs;

  switch(equation.kind_equation) {
    case CONST_EQ:
      {
#if DEBUG_MERGE
        const auto & rhs = equation.rhs;
        assert(lhs.isConstant() && rhs.isConstant());
        std::cout << "@merge. Merging constants" << std::endl
          << lhs << " and " << rhs << std::endl;
#endif
        pushPending(pending_to_propagate, equation);
        propagate();
      }
      break;
    case APPLY_EQ: 
      {
#if DEBUG_MERGE
        const auto & rhs = equation.rhs;
        assert(lhs.isReplaceable() && rhs.isConstant());
        std::cout << "@merge. Merging apply equations" << std::endl
          << lhs << " and " << rhs << std::endl;
#endif
        auto repr_lhs_first_argument = uf.find(lhs.getLeftId()), repr_lhs_second_argument = uf.find(lhs.getRightId());
        const EquationCurryNodes * element_found = lookup_table.query(repr_lhs_first_argument, repr_lhs_second_argument);

        if(element_found != nullptr){
#if DEBUG_MERGE
          std::cout << "@merge : Element found in lookup_table"
            << element_found << std::endl;
#endif
          pushPending(pending_to_propagate, PairEquationCurryNodes(equation, *element_found));
          propagate();
        }
        else{
          lookup_table.enter(repr_lhs_first_argument, repr_lhs_second_argument, &equation);
          use_list[repr_lhs_first_argument].push_back(&equation);
          use_list[repr_lhs_second_argument].push_back(&equation);
#if DEBUG_MERGE
          std::cout << "@merge: the element wasnt in the lookup table" << std::endl
            << "------------------------------------------" << std::endl
            << "Index lhs " << lhs.getLeftId()
            << "[repr:" << repr_lhs_first_argument << "] has this in UseList "
            << std::endl << equation << std::endl
            << "Index rhs " << lhs.getRightId()
            << "[repr:" << repr_lhs_second_argument << "] has this in UseList "
            << std::endl << equation << std::endl
            << "------------------------------------------" << std::endl;
#endif
        }
      }
      break;
  }
}

PendingElementsPointers CongruenceClosureExplain::explain(const z3::expr & lhs, const z3::expr & rhs){
  return explain(
      factory_curry_nodes.curry_nodes[lhs.id()]->getId(), 
      factory_curry_nodes.curry_nodes[rhs.id()]->getId());
}

PendingElementsPointers CongruenceClosureExplain::explain(EqClass x, EqClass y){
  PendingElementsPointers ans;
  if(ufe.find(x) != ufe.find(y))
    return ans; 
  UnionFind local_uf(ufe.getSize());
  ExplainEquations pending_proofs;

  pending_proofs.emplace_back(x, y);
  while(!pending_proofs.empty()){
    auto current_equation = pending_proofs.back();
    pending_proofs.pop_back();

    auto common_ancestor_x_y = nearestCommonAncestor(current_equation.source, current_equation.target, local_uf);
    explainAlongPath(current_equation.source, common_ancestor_x_y, local_uf, pending_proofs, ans);
    explainAlongPath(current_equation.target, common_ancestor_x_y, local_uf, pending_proofs, ans);
  }
  return ans;
}

std::ostream & CongruenceClosureExplain::giveExplanation(std::ostream & os, const z3::expr & lhs, const z3::expr & rhs){
  os << "Explain " << lhs << ", " << rhs << std::endl; 
  auto explanation = explain(lhs, rhs);
  if(explanation.size() == 0)
    return os << lhs << " and " << rhs << " belong to different equivalent classes" << std::endl;
  unsigned num = 1;
  for(auto z : explanation){
    os << "Label " << num++ << ":" << std::endl;
    os << *z << std::endl;
  }
  return os;
}

std::ostream & CongruenceClosureExplain::giveExplanation(std::ostream & os, EqClass lhs, EqClass rhs){
  os << "Explain " << lhs << ", " << rhs << std::endl; 
  auto explanation = explain(lhs, rhs);
  if(explanation.size() == 0)
    return os << lhs << " and " << rhs << " belong to different equivalent classes" << std::endl;
  unsigned num = 1;
  for(auto z : explanation){
    os << "Label " << num++ << ":" << std::endl;
    os << *z << std::endl;
  }
  return os;
}

Z3ElementsPointers CongruenceClosureExplain::z3Explain(const z3::expr & lhs, const z3::expr & rhs){
  throw "Not implemented yet"; 
} 

void CongruenceClosureExplain::explainAlongPath(EqClass a, EqClass c, 
    UnionFind & uf, ExplainEquations & pending_proofs, PendingElementsPointers & ans){
  a = highestNode(a, uf);
  while(a != c){
    auto b = ufe.parentProofForest(a);
    auto current_label = ufe.getLabel(a);

    switch(current_label->tag){
      case EQ_EQ:
        {
          auto first_equation = current_label->p_eq_cn.first;
          auto second_equation = current_label->p_eq_cn.second;
          EqClass a1 = first_equation.lhs.getLeftId(), a2 = first_equation.lhs.getRightId(),
                  b1 = second_equation.lhs.getLeftId(), b2 = second_equation.lhs.getRightId();
          pending_proofs.emplace_back(a1, b1);
          pending_proofs.emplace_back(a2, b2);
        }
        //ans.push_back(current_label);
        break;
      case EQ:
        ans.push_back(current_label);
        break;
    }
    uf.combine(b, a);
    a = highestNode(b, uf);
  }
}

void CongruenceClosureExplain::merge(){
  while(!equations_to_merge.empty()){
    const auto equations_to_merge_it = equations_to_merge.back();
    equations_to_merge.pop_back();

    switch(equations_to_merge_it->tag) {
      case EQ: 
        merge(equations_to_merge_it->eq_cn);
        break;
      case EQ_EQ:
        throw "Problem @ CongruenceClosureExplain::merge(). \
          This method cannot take as input a PairEquation.";
    }
  }
}

void CongruenceClosureExplain::propagate(){
  while(!pending_to_propagate.empty()){
    const auto pending_element = pending_to_propagate.back();
    pending_to_propagate.pop_back();

#if DEBUG_PROPAGATE
    std::cout << "|--------------------------------------------------------" << std::endl
      << "@propagate. Taking this element " << *pending_element << std::endl
      << "--------------------------------------------------------|" << std::endl;
#endif     

    const CurryNode & a = (pending_element->tag == EQ) ? pending_element->eq_cn.lhs : pending_element->p_eq_cn.first.rhs;
    const CurryNode & b = (pending_element->tag == EQ) ? pending_element->eq_cn.rhs : pending_element->p_eq_cn.second.rhs;
    EqClass repr_a = uf.find(a.getId()), repr_b = uf.find(b.getId());
    bool repr_a_is_common = (repr_a > subterms.size()) ? false : subterms[repr_a].is_common();
    bool repr_b_is_common = (repr_b > subterms.size()) ? false : subterms[repr_b].is_common();

#if DEBUG_PROPAGATE
    std::cout << "|------------------------------------------" << std::endl
      << "@propagate. To merge these two inside uf: " << std::endl
      << a << "(" << repr_a << ")" << std::endl
      << b << "(" << repr_b << ")" << std::endl
      << "------------------------------------------|" << std::endl;
#endif

    if(repr_a != repr_b) {
      // Invariant: The representative is choosen as follows:
      // If a' and b' are both common or uncommon, then break ties using their rank
      // Otherwise, pick the node who is common
      if((repr_a_is_common && repr_b_is_common) || (!repr_a_is_common && !repr_b_is_common)){
        if(uf.getRank(repr_a) <= uf.getRank(repr_b))
          propagateAux(a, b, repr_a, repr_b, *pending_element);
        else
          propagateAux(b, a, repr_b, repr_a, *pending_element);
      }
      if(repr_b_is_common)
          propagateAux(a, b, repr_a, repr_b, *pending_element);
      else
          propagateAux(b, a, repr_b, repr_a, *pending_element);
    }
  }
}

void CongruenceClosureExplain::propagateAux(const CurryNode & a, const CurryNode & b,
    EqClass repr_a, EqClass repr_b,
    const PendingElement & pending_element){
  EqClass old_repr_a = repr_a;
  uf.combine(b.getId(), a.getId(), &pending_element);

  for(auto equation = use_list[old_repr_a].begin(); equation != use_list[old_repr_a].end(); ){
    EqClass c1 = (*equation)->lhs.getLeftId(), c2 = (*equation)->lhs.getRightId();
    EqClass repr_c1 = uf.find(c1), repr_c2 = uf.find(c2);
    const EquationCurryNodes * element_found = lookup_table.query(repr_c1, repr_c2);

    if(element_found != nullptr){

#if DEBUG_PROPAGATE_AUX
      std::cout << "|------------------------------------------------" << std::endl
        << "@propagate. To add these to pending_to_propagate" << std::endl
        << "(" << **equation << ", " << std::endl
        << *element_found << ")" << std::endl
        << "-------------------------------------------------|" << std::endl;
#endif

      pushPending(pending_to_propagate, PairEquationCurryNodes(**equation, *element_found));
    }
    else{

#if DEBUG_PROPAGATE_AUX
      std::cout << "|-------------------------------------------------" << std::endl
        << "@propagate. Element not found in the lookup_table" << std::endl
        << "adding " << **equation << std::endl
        << "to the lookup_table and moving it to the use_list of " << repr_b << std::endl
        << "--------------------------------------------------------|" << std::endl;
#endif

      use_list[repr_b].push_back(*equation);
      lookup_table.enter(repr_c1, repr_c2, *equation);
    }
    equation = use_list[old_repr_a].erase(equation);
  }
  assert(use_list[old_repr_a].empty());
}

void CongruenceClosureExplain::buildCongruenceClosure(std::list<EqClass> & pending){
  throw "CongruenceClosureExplain::buildCongruenceClosure(std::list<EqClass> &). \
    Implementation not defined";
}

std::ostream & operator << (std::ostream & os, const CongruenceClosureExplain & cc){
  return os;
}
