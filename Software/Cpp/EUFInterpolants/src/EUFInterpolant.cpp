#include "EUFInterpolant.h"

EUFInterpolant::EUFInterpolant(Z3_context c, Z3_ast v) : cc(c, v) {

  unsigned rootNum = cc.getRootNum();

  // Traversing the graph to compute 
  // if a term is common or not
  
  /*
    for(unsigned i = 0; i < totalNumVertex; ++i){
    Vertex * _tempVertex = cc.getTerm(i);
    if(_tempVertex->getId() == find(_tempVertex)->getId()){
      
    }
    }
  */

  
}

EUFInterpolant::EUFInterpolant(Z3_context c, Z3_ast v, std::set<std::string> & symbolsToElim) :
  cc(c, v, symbolsToElim){
  
  identifyCommonSymbols();

  unsigned total = Vertex::getTotalNumVertex();
  for(unsigned i = 0; i < total; ++i){
    std::cout << cc.getTerm(i)->to_string() << " " << cc.getTerm(i)->getSymbolCommonQ() << std::endl;
  }
  
  
  /*
    for(unsigned i = 0; i < totalNumVertex; ++i){
    Vertex * _tempVertex = cc.getTerm(i);
    if(_tempVertex->getId() == find(_tempVertex)->getId()){
      
    }
    }
  */
  
}

EUFInterpolant::~EUFInterpolant(){
}

void EUFInterpolant::algorithm(){
}

void EUFInterpolant::identifyCommonSymbols(){
  unsigned rootNum = cc.getRootNum();
  std::stack<Vertex*> s;
  Vertex * root = cc.getTerm(rootNum), * _tempRoot;
  unsigned _arity;
  std::set<std::string> & sTE = cc.getSymbolsToElim();
  
  // Traversing the graph (in post-order) 
  // to determine if a term is common or not
  do{
    while(root != nullptr){
      _arity = root->getArity();
      switch(_arity){
      case 0:
	s.push(root);
	root = nullptr;
	break;
      case 1:
	s.push(root);
	root = root->getLeftChild();
	break;
      case 2:
	s.push(root->getRightChild()), s.push(root);
	root = root->getLeftChild();
	break;
      default:
	break;
      }
    } 
    root = s.top(), s.pop();
    _arity = root->getArity();
    if(_arity == 2 && !s.empty() && root->getRightChild()->getId() == s.top()->getId()){
      _tempRoot = s.top();
      s.pop();
      s.push(root);
      root = _tempRoot;
    }
    else{
      // do something with root
      //std::cout << *root << std::endl;
      std::string _tempName = root->getName();
      bool _tempCSQ = (sTE.find(_tempName) == sTE.end()) ? true : false;
      std::vector<Vertex*> _tempSuccessors = root->getSuccessors();
      for(unsigned i = 0; i < _arity; ++i){
	if(!_tempCSQ)
	  break;
	_tempCSQ = _tempCSQ && _tempSuccessors[i]->getSymbolCommonQ();
      }
      root->setSymbolCommonQ(_tempCSQ);
      root = nullptr;
    }
  } while(!s.empty());
}

std::ostream & EUFInterpolant::print(std::ostream & os){
  return os;
}

