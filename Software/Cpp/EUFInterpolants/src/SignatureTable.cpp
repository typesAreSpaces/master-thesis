#include "SignatureTable.h"

SignatureTable::SignatureTable(Z3_context c, Z3_ast v) :
  Terms(c, v) {}

SignatureTable::SignatureTable(Z3_context c, Z3_ast v,
			       std::set<std::string> & symbolsToElim) :
  Terms(c, v, symbolsToElim) {}

SignatureTable::SignatureTable(std::istream & in) :
  Terms(in) {}

SignatureTable::~SignatureTable(){}

void SignatureTable::enter(Term* v){
  unsigned _arity = v->getArity();
  if(_arity == 1){
    //<UnarySignature, Term*>
    unaryTable.insert(std::make_pair(getUnarySignature(v), v));
  }
  if(_arity == 2){
    //<BinarySignature, Term*>
    binaryTable.insert(std::make_pair(getBinarySignature(v), v));
  }
  return;
}

void SignatureTable::remove(Term * v){
  unsigned _arity = v->getArity();
  try{
    query(v);
    if(_arity == 1)
      unaryTable.erase(getUnarySignature(v));
    if(_arity == 2)
      binaryTable.erase(getBinarySignature(v));
  }
  catch(const char * msg){
    //std::cerr << "SignatureTable::remove error" << std::endl;
    //std::cerr << msg << std::endl;
  }
  return;
}

Term * SignatureTable::query(Term * v){
  unsigned _arity = v->getArity();
  if(_arity == 1){
    UnaryTerms::iterator it = unaryTable.find(getUnarySignature(v));
    if(it == unaryTable.end())
      throw "Element not found";
    return it->second;
  }
  else{
    if(_arity == 2){
      BinaryTerms::iterator it = binaryTable.find(getBinarySignature(v));
      if(it == binaryTable.end())
	throw "Element not found";
      return it->second;
    }
    else
      throw "Wrong arity";
  }
}

UnarySignature SignatureTable::getUnarySignature(Term * v){
  std::vector<Term*> _successors = v->getSuccessors();
  // Store v with its current signature
  return UnarySignature(v->getName(),
			getReprTerm(_successors[0])->getId());
}

BinarySignature SignatureTable::getBinarySignature(Term * v){
  std::vector<Term*> _successors = v->getSuccessors();
  // Store v with its current signature
  return BinarySignature(v->getName(),
			 getReprTerm(_successors[0])->getId(),
			 getReprTerm(_successors[1])->getId());
}

std::ostream & operator << (std::ostream & os, SignatureTable & st){
  os << "Signature Table" << std::endl;
  for(auto it = st.unaryTable.begin(); it != st.unaryTable.end(); ++it){
    UnarySignature _temp = it->first;
    os << _temp << " " << *(it->second) << std::endl;
  }
  for(auto it = st.binaryTable.begin(); it != st.binaryTable.end(); ++it){
    BinarySignature __temp = it->first;
    os << __temp << " " << *(it->second) << std::endl;
  }
  return os;
}
