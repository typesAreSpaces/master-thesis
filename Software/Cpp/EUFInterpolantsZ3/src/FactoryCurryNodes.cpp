#include "FactoryCurryNodes.h"

FactoryCurryNodes::FactoryCurryNodes(const unsigned & num_terms, const CurryDeclarations & curry_decl) :
  num_terms(num_terms), curry_decl(curry_decl){
  curry_nodes.resize(num_terms);
}

FactoryCurryNodes::~FactoryCurryNodes(){
  for(auto x : hash_table)
    delete x.second;
}

CurryNode * FactoryCurryNodes::newCurryNode(unsigned id, std::string func_name,
					    CurryNode * left, CurryNode * right){
  std::size_t index = 0;
  // We shouldnt distinguish if nodes have different ids
  // hash_combine(index, id, unsigned_hasher); 
  hash_combine(index, func_name, string_hasher);
  hash_combine(index, left, curry_hasher);
  hash_combine(index, right, curry_hasher);

  auto element = hash_table.find(index);
  if(element != hash_table.end()){
    return element->second;
  }
  else{
    auto new_element = new CurryNode(id, func_name, left, right);
    if(id_table.size() <= id)
      id_table.resize(id + 1);
    id_table[id] = new_element;
    hash_table[index] = new_element;
    if(left)
      curry_predecessors[left].push_back(PredPair(new_element, LHS));
    if(right)
      curry_predecessors[right].push_back(PredPair(new_element, RHS));
    if(new_element->isReplaceable())
      to_replace.push_back(new_element);
    return new_element;
  }
}

CurryNode * FactoryCurryNodes::getCurryNode(std::size_t index) const {
  auto element = hash_table.find(index);
  if(element != hash_table.end())
    return element->second;
  throw "Problem @ FactoryCurryNodes::getCurryNode(std::size_t). Element not found.";
}

const unsigned FactoryCurryNodes::size() const {
  return curry_nodes.size() + extra_nodes.size();
}

const unsigned FactoryCurryNodes::uniqueSize() const {
  return hash_table.size();
}

unsigned FactoryCurryNodes::addExtraNodes(unsigned num){
  unsigned last_node_pos = extra_nodes.size(),
    new_last_node_pos = last_node_pos + num;
  extra_nodes.resize(new_last_node_pos);
  return new_last_node_pos;
}

void FactoryCurryNodes::updatePreds(CurryNode * from, CurryNode * to){
  curry_predecessors[to].splice(curry_predecessors[to].end(), curry_predecessors[from]);

  for(auto pred_pair : curry_predecessors[to]){
    switch(pred_pair.side_of_equation){
    case LHS:
      pred_pair.pred->updateLeft(to);
      break;
    case RHS:
      pred_pair.pred->updateRight(to);
      break;
    }
    if(pred_pair.pred->isReplaceable())
      to_replace.push_back(pred_pair.pred);
  }  
  return;
}

void FactoryCurryNodes::curryficationHelper(z3::expr const & e, std::vector<bool> & visited, IdsToMerge & ids_to_merge){
  if(e.is_app()){

    if(visited[e.id()]) return;
    
    visited[e.id()] = true;
    unsigned num = e.num_args();
    auto f = e.decl();
    
    for(unsigned i = 0; i < num; i++)
      curryficationHelper(e.arg(i), visited, ids_to_merge);
    
    // Update curry_nodes
    if(num > 0){
      unsigned last_node_pos = extra_nodes.size();
      unsigned new_last_node_pos = addExtraNodes(num);
      
      // Case for first argument
      extra_nodes[last_node_pos] =
	newCurryNode(last_node_pos + num_terms,
		     "apply",
		     curry_decl.at(f.id()),
		     curry_nodes[e.arg(0).id()]);
      // Case for the rest of the arguments
      for(unsigned i = 1; i < num; i++)
	extra_nodes[last_node_pos + i] =
	  newCurryNode(last_node_pos + i + num_terms,
		       "apply",
		       extra_nodes[last_node_pos + i - 1],
		       curry_nodes[e.arg(i).id()]);
      curry_nodes[e.id()] = extra_nodes[new_last_node_pos - 1];
    }
    else
      curry_nodes[e.id()] = curry_decl.at(f.id());

    switch(f.decl_kind()){
    case Z3_OP_EQ:
      ids_to_merge.push_back(EquationZ3Ids(e.arg(0).id(), e.arg(1).id()));
      return;
    default:
      return;
    }
  }
  
  throw "Problem @ FactoryCurryNodes::curryficationHelper\
(z3::expr const &, std::vector<bool> &). The z3::expr const & is not an app.";
}

IdsToMerge FactoryCurryNodes::curryfication(z3::expr const & e){
  std::vector<bool> visited(num_terms, false);
  std::list<EquationZ3Ids> ids_to_merge;
  curryficationHelper(e, visited, ids_to_merge);
  return ids_to_merge;
}

void FactoryCurryNodes::flattening(const unsigned & min_id, PendingExplain & pending_explain){
  while(!to_replace.empty()){
    auto cur_curry_node = to_replace.back();
    to_replace.pop_back();

    unsigned last_node_pos = extra_nodes.size();
    extra_nodes.push_back(newCurryNode(last_node_pos + num_terms,
				       "fresh_" + std::to_string(last_node_pos + num_terms),
				       nullptr, nullptr));
    CurryNode * new_constant = extra_nodes[last_node_pos];
    pending_explain.push_back(PendingElement(EquationCurryNodes(cur_curry_node, new_constant)));
    updatePreds(cur_curry_node, new_constant);
  }
  // Update Z3 Ids
  for(unsigned i = min_id; i < curry_nodes.size(); i++)
    curry_nodes[i]->updateZ3Id(i);
  for(auto x : pending_explain){
    x.eq_cn.rhs->updateZ3Id(x.eq_cn.lhs->getZ3Id());
  }
}

std::ostream & operator << (std::ostream & os, const FactoryCurryNodes & fcns){

  for(auto x : fcns.hash_table)
    std::cout << *(x.second) << std::endl;
  
  os << "Size of FactoryCurryNodes: " << fcns.hash_table.size() << std::endl;
  return os;
}
