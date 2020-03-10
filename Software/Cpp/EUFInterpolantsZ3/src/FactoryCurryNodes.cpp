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
    return new_element;
  }
}

CurryNode * FactoryCurryNodes::getCurryNode(std::size_t index){
  auto element = hash_table.find(index);
  if(element != hash_table.end())
    return element->second;
  throw "Problem @ FactoryCurryNodes::getCurryNode(std::size_t). Element not found.";
}
