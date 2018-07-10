#include "signatureTable.h"

SignatureTable::SignatureTable(GTerms & gterms):
  gterms(gterms) {}

SignatureTable::~SignatureTable(){}

void SignatureTable::enter(Vertex* v){
  int _arity = v->getArity();  
  std::vector<Vertex*> _successors = v->getSuccessors();
  if(_arity == 1){
    //<signatureArg1, Vertex*>
    table1.insert(std::make_pair(
				 signatureArg1(
					       v->getName(),
					       gterms.getEC().find(_successors[0]->getId())
					      ),
				 v));
  }
  if(_arity == 2){
    //<signatureArg2, Vertex*>
    table2.insert(std::make_pair(
				 signatureArg2(
					       v->getName(),
					       gterms.getEC().find(_successors[0]->getId()),
					       gterms.getEC().find(_successors[1]->getId())
					      ),
				 v));
  }
  return;
}

void SignatureTable::remove(Vertex * v){
  int _arity = v->getArity();
  std::vector<Vertex*> _successors = v->getSuccessors();
  if(_arity == 1){
    try{
      Vertex * _temp = query(v);
      table1.erase(signatureArg1(
				 v->getName(),
				 gterms.getEC().find(_successors[0]->getId())
				));
    }
    catch(const char* msg){
    }
  }
  if(_arity == 2){
    try{
      Vertex * _temp = query(v);
      table2.erase(signatureArg2(
				 v->getName(),
				 gterms.getEC().find(_successors[0]->getId()),
				 gterms.getEC().find(_successors[1]->getId())
				));
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
    treeArg1::iterator it = table1.find(signatureArg1(
						      v->getName(),
						      gterms.getEC().find(_successors[0]->getId())
						     ));
    if(it == table1.end())
      throw "Element not found";
    return it->second;
  }
  else{
    if(_arity == 2){
    treeArg2::iterator it = table2.find(signatureArg2(
						      v->getName(),
						      gterms.getEC().find(_successors[0]->getId()),
						      gterms.getEC().find(_successors[1]->getId())
						     ));
    if(it == table2.end())
      throw "Element not found";
    return it->second;
    }
    else
      throw "Wrong arity";
  }
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
