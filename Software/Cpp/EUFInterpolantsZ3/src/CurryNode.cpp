#include "CurryNode.h"

CurryNode::CurryNode(unsigned id) :
  id(id), func_name(""),
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

std::ostream & operator << (std::ostream & os, const CurryNode & cn){
  os << cn.id << ". " << cn.func_name;
  if(cn.left != nullptr)
    os << " Left: " << *cn.left;
  if(cn.right != nullptr)
    os << " Right: " << *cn.right;
  return os;
}
