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
    table1.insert(std::make_pair(getUnarySignature(v), v));
  }
  if(_arity == 2){
    //<BinarySignature, Term*>
    table2.insert(std::make_pair(getBinarySignature(v), v));
  }
  return;
}

void SignatureTable::remove(Term * v){
  unsigned _arity = v->getArity();
  try{
    query(v);
    if(_arity == 1)
      table1.erase(getUnarySignature(v));
    if(_arity == 2)
      table2.erase(getBinarySignature(v));
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
    UnaryTerms::iterator it = table1.find(getUnarySignature(v));
    if(it == table1.end())
      throw "Element not found";
    return it->second;
  }
  else{
    if(_arity == 2){
      BinaryTerms::iterator it = table2.find(getBinarySignature(v));
      if(it == table2.end())
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
			getTerm(_successors[0])->getId());
}

BinarySignature SignatureTable::getBinarySignature(Term * v){
  std::vector<Term*> _successors = v->getSuccessors();
  // Store v with its current signature
  return BinarySignature(v->getName(),
			 getTerm(_successors[0])->getId(),
			 getTerm(_successors[1])->getId());
}

std::ostream & operator << (std::ostream & os, SignatureTable & st){
  os << "Signature Table" << std::endl;
  for(auto it = st.table1.begin(); it != st.table1.end(); ++it){
    UnarySignature _temp = it->first;
    os << _temp << " " << *(it->second) << std::endl;
  }
  for(auto it = st.table2.begin(); it != st.table2.end(); ++it){
    BinarySignature __temp = it->first;
    os << __temp << " " << *(it->second) << std::endl;
  }
  return os;
}
