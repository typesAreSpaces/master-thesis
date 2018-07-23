#include "SignatureTable.h"

SignatureTable::SignatureTable(Z3_context c, Z3_ast v) :
  GTerms(c, v) {}

SignatureTable::SignatureTable(std::istream & in) :
  GTerms(in) {}

SignatureTable::~SignatureTable(){}

void SignatureTable::enter(Vertex* v){
  int _arity = v->getArity();  
  if(_arity == 1){
    //<signatureArg1, Vertex*>
    table1.insert(std::make_pair(getSignatureArg1(v), v));
  }
  if(_arity == 2){
    //<signatureArg2, Vertex*>
    table2.insert(std::make_pair(getSignatureArg2(v), v));
  }
  return;
}

void SignatureTable::remove(Vertex * v){
  int _arity = v->getArity();
  if(_arity == 1){
    try{
      Vertex * _temp = query(v);
      table1.erase(getSignatureArg1(v));
    }
    catch(const char* msg){
    }
  }
  if(_arity == 2){
    try{
      Vertex * _temp = query(v);
      table2.erase(getSignatureArg2(v));
    }
    catch(const char* msg){
    }
  }
  return;
}

Vertex * SignatureTable::query(Vertex * v){
  int _arity = v->getArity();
  std::vector<Vertex*> _successors = v->getSuccessors();
  if(_arity == 1){
    treeArg1::iterator it = table1.find(getSignatureArg1(v));
    if(it == table1.end())
      throw "Element not found";
    return it->second;
  }
  else{
    if(_arity == 2){
    treeArg2::iterator it = table2.find(getSignatureArg2(v));
    if(it == table2.end())
      throw "Element not found";
    return it->second;
    }
    else
      throw "Wrong arity";
  }
}

signatureArg1 SignatureTable::getSignatureArg1(Vertex * v){
  int _arity = v->getArity();
  std::vector<Vertex*> _successors = v->getSuccessors();
  return signatureArg1(v->getName(),
		       find(_successors[0])->getId());
}

signatureArg2 SignatureTable::getSignatureArg2(Vertex * v){
  int _arity = v->getArity();
  std::vector<Vertex*> _successors = v->getSuccessors();
  return signatureArg2(v->getName(),
		       find(_successors[0])->getId(),
		       find(_successors[1])->getId());
}

std::ostream & SignatureTable::print(std::ostream & os){
  for(treeArg1::iterator it = table1.begin(); it != table1.end(); ++it){
    signatureArg1 _temp = it->first;
    os << _temp << " " << *(it->second) << std::endl;
  }
  for(treeArg2::iterator it = table2.begin(); it != table2.end(); ++it){
    signatureArg2 __temp = it->first;
    os << __temp << " " << *(it->second) << std::endl;
  }
  return os;
}
