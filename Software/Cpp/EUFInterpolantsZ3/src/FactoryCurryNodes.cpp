#include "FactoryCurryNodes.h"

FactoryCurryNodes::FactoryCurryNodes(){
}

FactoryCurryNodes::~FactoryCurryNodes(){
  for(auto x : hash_table)
    delete x.second;
}

CurryNode * FactoryCurryNodes::newCurryNode(unsigned id, std::string func_name, CurryNode * left, CurryNode * right){
  std::size_t index = 0;
  // hash_combine(index, id, unsigned_hasher); // We cant distinguish if the node have different id's
  hash_combine(index, func_name, string_hasher);
  hash_combine(index, left, curry_hasher);
  hash_combine(index, right, curry_hasher);

  auto element = hash_table.find(index);
  if(element != hash_table.end()){
    return element->second;
  }
  else{
    auto new_element = new CurryNode(id, func_name, left, right);
    
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

void FactoryCurryNodes::transferPreds(CurryNode * from, CurryNode * to){
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

void FactoryCurryNodes::flattening(CurryNodes & extra_nodes, unsigned num_terms){
  while(!to_replace.empty()){
    auto cur_curry_node = to_replace.back();
    to_replace.pop_back();

    unsigned last_node_pos = extra_nodes.size();
    extra_nodes.push_back(newCurryNode(last_node_pos + num_terms,
				       "fresh_" + std::to_string(last_node_pos + num_terms),
				       nullptr, nullptr));
    auto new_constant = extra_nodes[last_node_pos];
    // TODO: Include a merge of cur_curry_node and new_constant
    std::cout << "To merge: " << *cur_curry_node << " = " << *new_constant << std::endl;
    transferPreds(cur_curry_node, new_constant);
  }
}

std::ostream & operator << (std::ostream & os, const FactoryCurryNodes & fcns){

  for(auto x : fcns.hash_table)
    std::cout << *(x.second) << std::endl;
  
  os << "Size of FactoryCurryNodes: " << fcns.hash_table.size() << std::endl;
  return os;
}
