#include "CurryNode.h"

std::hash<unsigned>                         CurryNode::unsigned_hasher;
std::hash<std::string>                      CurryNode::string_hasher;
std::hash<CurryNode*>                       CurryNode::curry_hasher;
std::unordered_map<std::size_t, CurryNode*> CurryNode::hash_table;

CurryNode::CurryNode(unsigned id, std::string func_name, CurryNode * left, CurryNode * right) :
  id(id), func_name(func_name), left(left), right(right) {
}

const bool CurryNode::isConstant() const {
  return (left == nullptr) && (right == nullptr);
}

const bool CurryNode::isReplaceable() const {
  if(left == nullptr || right == nullptr)
    return false;
  return left->isConstant() && right->isConstant();
}

std::size_t CurryNode::hash(){
  std::size_t key = 0;
  // hash_combine(key, id, unsigned_hasher); // We cant distinguish if the node have different id's
  hash_combine(key, func_name, string_hasher);
  hash_combine(key, left, curry_hasher);
  hash_combine(key, right, curry_hasher);
  return key;
}

std::ostream & operator << (std::ostream & os, const CurryNode & cn){
  for(unsigned i = 0; i < cn.space; i++)
     os << " ";
  if(cn.space == 1)
    os << "* ";
  os << cn.id << ". " << cn.func_name << std::endl;
  if(cn.left != nullptr){
    (cn.left->space)+=cn.space;
    for(unsigned i = 0; i < cn.space; i++)
      os << " ";
    os << "Left" << std::endl;
    os << *cn.left;
    (cn.left->space)-=cn.space;
  }
  if(cn.right != nullptr){
    (cn.right->space)+=cn.space;
    for(unsigned i = 0; i < cn.space; i++)
      os << " ";
    os << "Right" << std::endl;
    os << *cn.right;
    (cn.right->space)-=cn.space;
  }
  return os;
}

void * CurryNode::operator new (std::size_t size, unsigned id, std::string func_name, CurryNode * left, CurryNode * right){
  std::size_t key = 0;
  // hash_combine(key, id, unsigned_hasher); // We cant distinguish if the node have different id's
  hash_combine(key, func_name, string_hasher);
  hash_combine(key, left, curry_hasher);
  hash_combine(key, right, curry_hasher);

  auto element = CurryNode::hash_table.find(key);
  if(element != CurryNode::hash_table.end()){
    return element->second;
  }
  else{
    auto new_element = ::new CurryNode(id, func_name, left, right);
    CurryNode::hash_table[key] = new_element;
    return new_element;
  }
}

CurryNode * CurryNode::newCurryNode(unsigned id, std::string func_name, CurryNode * left, CurryNode * right){
  auto ans = new(id, func_name, left, right) CurryNode(id, func_name, left, right);
  return ans;
}

void CurryNode::removePointers(){
  for(auto x : CurryNode::hash_table)
    delete x.second;
}
