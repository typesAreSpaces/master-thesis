#include "SignatureTable.h"

SignatureTable::SignatureTable(Z3_context c, Z3_ast v) :
  Terms(c, v) {}

SignatureTable::SignatureTable(Z3_context c, Z3_ast v, std::set<std::string> & symbolsToElim) :
  Terms(c, v, symbolsToElim) {}

SignatureTable::SignatureTable(std::istream & in) :
  Terms(in) {}

SignatureTable::~SignatureTable(){}

void SignatureTable::enter(Vertex* v){
  unsigned _arity = v->getArity();
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
  unsigned _arity = v->getArity();
	try{
		query(v);
		if(_arity == 1)
			table1.erase(getSignatureArg1(v));
		if(_arity == 2)
			table2.erase(getSignatureArg2(v));
	}
	catch(const char * msg){
		//std::cerr << "SignatureTable::remove error" << std::endl;
		//std::cerr << msg << std::endl;
	}
  return;
}

Vertex * SignatureTable::query(Vertex * v){
  unsigned _arity = v->getArity();
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
  std::vector<Vertex*> _successors = v->getSuccessors();
  return signatureArg1(v->getName(),
											 getVertex(_successors[0])->getId());
}

signatureArg2 SignatureTable::getSignatureArg2(Vertex * v){
  std::vector<Vertex*> _successors = v->getSuccessors();
  return signatureArg2(v->getName(),
											 getVertex(_successors[0])->getId(),
											 getVertex(_successors[1])->getId());
}

std::ostream & operator << (std::ostream & os, SignatureTable & st){
	os << "Signature Table" << std::endl;
  for(treeArg1::iterator it = st.table1.begin(); it != st.table1.end(); ++it){
    signatureArg1 _temp = it->first;
    os << _temp << " " << *(it->second) << std::endl;
  }
  for(treeArg2::iterator it = st.table2.begin(); it != st.table2.end(); ++it){
    signatureArg2 __temp = it->first;
    os << __temp << " " << *(it->second) << std::endl;
  }
  return os;
}
