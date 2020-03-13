#include "CurryNode.h"
#define OS_FULL true

CurryNode::CurryNode(unsigned id, std::string func_name, CurryNode * left, CurryNode * right) :
  id(id), z3_id(0), const_id(0), func_name(func_name), left(left), right(right) {
}

const bool CurryNode::isConstant() const {
  return (left == nullptr) && (right == nullptr);
}

const bool CurryNode::isReplaceable() const {
  if(left == nullptr || right == nullptr)
    return false;
  return left->isConstant() && right->isConstant();
}

const bool CurryNode::isDefined() const {
  return z3_id_defined;
}

void CurryNode::updateLeft(CurryNode * new_left){
  left = new_left;
  return;
}

void CurryNode::updateRight(CurryNode * new_right){
  right = new_right;
  return;
}

void CurryNode::updateZ3Id(unsigned new_z3_id){
  z3_id = new_z3_id;
  z3_id_defined = true;
  return;
}

void CurryNode::updateConstId(unsigned new_const_id){
  const_id = new_const_id;
  return;
}

const unsigned CurryNode::getId() const {
  return id;
}

const unsigned CurryNode::getLeftId() const {
  if(left == nullptr)
    throw "Problem @ CurryNode::getLeftId(). left is a nullptr.";
  return left->id;
}

const unsigned CurryNode::getRightId() const {
  if(right == nullptr)
    throw "Problem @ CurryNode::getRightId(). right is a nullptr.";
  return right->id;
}

const unsigned CurryNode::getZ3Id() const {
  return z3_id;
}

const unsigned CurryNode::getConstId() const {
  return const_id;
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
#if OS_FULL
  os << cn.id << "(Z3 id: " << cn.z3_id
     << "|Const id: " << cn.const_id << ")("
     << (cn.z3_id_defined ? "Defined" : "Not defined yet") << "). "
     << cn.func_name << std::endl;
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
#else
  os << cn.id << ". " << cn.func_name;
#endif
  return os;
}
