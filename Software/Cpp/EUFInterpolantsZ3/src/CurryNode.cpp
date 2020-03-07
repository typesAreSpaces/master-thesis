#include "CurryNode.h"

CurryNode::CurryNode(unsigned id) :
  id(id), func_name("fresh_" + std::to_string(id)),
  left(nullptr), right(nullptr) {
}

CurryNode::CurryNode(unsigned id, std::string func_name, CurryNode * left, CurryNode * right) :
  id(id), func_name(func_name), left(left), right(right) {
}

CurryNode::CurryNode(const CurryNode & cn) :
  id(cn.id), func_name(cn.func_name), left(cn.left), right(cn.right) {
}

void CurryNode::update(std::string new_name, CurryNode * new_left, CurryNode * new_right){
  func_name = new_name;
  left = new_left;
  right = new_right;
  return;
}

void CurryNode::changeId(unsigned new_id){
  id = new_id;
  return;
}

const unsigned CurryNode::getId() const {
  return id;
}

const bool CurryNode::isConstant() const {
  return (left == nullptr) && (right == nullptr);
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
