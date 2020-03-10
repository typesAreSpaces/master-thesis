#include "CurryNode.h"

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
  // -------------------------------------
  // Temporarily -------------------------
  // std::hash<unsigned>    unsigned_hasher;
  std::hash<std::string> string_hasher;
  std::hash<CurryNode*>  curry_hasher;
  // -------------------------------------
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
