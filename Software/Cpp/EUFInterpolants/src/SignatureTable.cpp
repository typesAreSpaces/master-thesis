#include "SignatureTable.h"

SignatureTable::SignatureTable(){};

SignatureTable::~SignatureTable(){}

void SignatureTable::enter(Term* v, UnionFind & eq_class){
  switch(v->getArity()){
  case 1:
    //<UnarySignature, Term*>
    unaryTable.insert(std::make_pair(getUnarySignature(v, eq_class), v));
    break;
  case 2:
    //<BinarySignature, Term*>
    binaryTable.insert(std::make_pair(getBinarySignature(v, eq_class), v));
    break;
  default:
    break;
  }
  return;
}

void SignatureTable::remove(Term * v, UnionFind & eq_class){
  try{
    query(v, eq_class);
    switch(v->getArity()){
    case 1:
      unaryTable.erase(getUnarySignature(v, eq_class));
      break;
    case 2:
      binaryTable.erase(getBinarySignature(v, eq_class));
      break;
    default:
      break;
    }
  }
  catch(const char * msg){
    //std::cerr << "SignatureTable::remove error" << std::endl;
    //std::cerr << msg << std::endl;
  }
  return;
}

Term * SignatureTable::query(Term * v, UnionFind & eq_class){
  unsigned arity = v->getArity();
  if(arity == 1){
    UnaryTerms::iterator it = unaryTable.find(getUnarySignature(v, eq_class));
    if(it == unaryTable.end())
      throw "Element not found";
    return it->second;
  }
  else if(arity == 2){
    BinaryTerms::iterator it = binaryTable.find(getBinarySignature(v, eq_class));
    if(it == binaryTable.end())
      throw "Element not found";
    return it->second;
  }
  else{
    throw "Wrong arity";
  }
}

UnarySignature SignatureTable::getUnarySignature(Term * v, UnionFind & eq_class){
  assert(v->getArity() == 1);
  std::vector<Term*> _successors = v->getSuccessors();
  // Store v with its current signature
  return UnarySignature(v->getName(),
			eq_class.find(_successors[0]->getId()));
}

BinarySignature SignatureTable::getBinarySignature(Term * v, UnionFind & eq_class){
  assert(v->getArity() == 2);
  std::vector<Term*> _successors = v->getSuccessors();
  // Store v with its current signature
  return BinarySignature(v->getName(),
			 eq_class.find(_successors[0]->getId()),
			 eq_class.find(_successors[1]->getId()));
}

std::ostream & operator << (std::ostream & os, const SignatureTable & st){
  os << "Signature Table" << std::endl;
  os << "Unary Terms:" << std::endl;
  for(auto it = st.unaryTable.begin(); it != st.unaryTable.end(); ++it)
    os <<  *(it->second) << " " << it->first << std::endl;
  os << "Binary Terms:" << std::endl;
  for(auto it = st.binaryTable.begin(); it != st.binaryTable.end(); ++it)
    os <<  *(it->second) << " " << it->first << std::endl;
  return os << std::endl;
}
