#include "EUFInterpolant.h"

EUFInterpolant::EUFInterpolant(Z3_context c, Z3_ast v) : cc(c, v) {
  algorithm();
}

EUFInterpolant::EUFInterpolant(Z3_context c, Z3_ast v, std::set<std::string> & symbolsToElim) : cc(c, v, symbolsToElim){
  algorithm();
}

EUFInterpolant::~EUFInterpolant(){
}

void EUFInterpolant::algorithm(){
  identifyCommonSymbols();
  cc.algorithm();
  setCommonRepresentatives();
  eliminationOfUncommonFSyms(); 
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
      symbolPos[_tempName].insert(root->getId());
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

  // Just to check
  /*
  unsigned total = Vertex::getTotalNumVertex();
  for(unsigned i = 0; i < total; ++i){
    std::cout << cc.getTerm(i)->to_string() << " " << cc.getTerm(i)->getSymbolCommonQ() << std::endl;
  }
  */
}

void EUFInterpolant::setCommonRepresentatives(){
  unsigned totalNV = Vertex::getTotalNumVertex();
  
  for(unsigned i = 0; i < totalNV; ++i){
    Vertex * _temp = cc.getTerm(i);
    if(!cc.find(_temp)->getSymbolCommonQ() && _temp->getSymbolCommonQ())
      cc.rotate(_temp, cc.find(_temp));
  }
}

void EUFInterpolant::eliminationOfUncommonFSyms(){
  for(symbolLoc::iterator it = symbolPos.begin(); it != symbolPos.end(); ++it){
    for(std::set<int>::iterator it2 = it->second.begin();
	it2 != it->second.end(); ++it2){
      // TODO
      std::cout << *it2 << std::endl;
    }
  }
}

std::ostream & EUFInterpolant::print(std::ostream & os){
  return os;
}

