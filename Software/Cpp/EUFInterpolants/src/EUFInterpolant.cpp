#include "EUFInterpolant.h"

EUFInterpolant::EUFInterpolant(Z3_context c, Z3_ast v) :
  cc(c, v), hC(cc.getTerms()), ctx(c) {
}

EUFInterpolant::EUFInterpolant(Z3_context c, Z3_ast v, std::set<std::string> & symbolsToElim) :
  cc(c, v, symbolsToElim), hC(cc.getTerms()), ctx(c) {
}

EUFInterpolant::~EUFInterpolant(){
}

void EUFInterpolant::algorithm(){
  identifyCommonSymbols();
	// Congruence Closure Algorithm
  cc.algorithm();
  setCommonRepresentatives();

	// TODO: FIX THIS!
  eliminationOfUncommonFSyms();
	addNegativeHornClauses();
  hC.conditionalElimination();

	std::cout << hC << std::endl;
	
	std::vector<HornClause*> hCS = hC.getHornClauses();
	std::cout << "Horn equations produced:" << std::endl;
	for(std::vector<HornClause*>::iterator it = hCS.begin();
			it != hCS.end(); ++it){
		std::cout << **it << std::endl;
	}
	
	std::cout << "Original Equations:" << std::endl;
	std::vector<std::pair<Z3_ast, Z3_ast> > a = cc.getEquations();
	for(std::vector<std::pair<Z3_ast, Z3_ast> >::iterator it = a.begin();
			it != a.end(); ++it){
	  display_ast(ctx, stdout, it->first);
		std::cout << " = ";
		display_ast(ctx, stdout, it->second);
		std::cout << std::endl;
	}

	std::cout << "Original Disequations:" << std::endl;
	std::vector<std::pair<Z3_ast, Z3_ast> > b = cc.getDisequations();
	for(std::vector<std::pair<Z3_ast, Z3_ast> >::iterator it = b.begin();
			it != b.end(); ++it){
		display_ast(ctx, stdout, it->first);
		std::cout << " ~= ";
		display_ast(ctx, stdout, it->second);
		std::cout << std::endl;
	}

	// Continue Here
	
}

void EUFInterpolant::identifyCommonSymbols(){
  unsigned rootNum = cc.getRootNum();
  std::stack<Vertex*> s;
  Vertex * root = cc.getVertex(rootNum), * _tempRoot;
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
    if(_arity == 2 && !s.empty()
       && root->getRightChild()->getId() == s.top()->getId()){
      _tempRoot = s.top();
      s.pop();
      s.push(root);
      root = _tempRoot;
    }
    else{
      // do something with root
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
}

void EUFInterpolant::setCommonRepresentatives(){
  unsigned totalNV = Vertex::getTotalNumVertex();
  for(unsigned i = 0; i < totalNV; ++i){
    Vertex * _temp = cc.getOriginalVertex(i);
    // A rotation between the current 
    // representative and the current term if:
    // 1) the current term is common
    // 2) the current term has a smaller arity
    if(_temp->getSymbolCommonQ()
       && _temp->getArity() < cc.getVertex(_temp)->getArity()){
      cc.rotate(_temp, cc.getVertex(_temp));
		}
  }
}

void EUFInterpolant::eliminationOfUncommonFSyms(){
  bool expose = false;
  for(symbolLoc::iterator it = symbolPos.begin();
      it != symbolPos.end(); ++it){
    for(std::set<unsigned>::iterator it2 = it->second.begin();
				it2 != it->second.end(); ++it2){
      if(!cc.getVertex(*it2)->getSymbolCommonQ()){
				expose = true;
				break;
      }
    }
		// We don't include in the Exposure method new introduced symbols
		// nor equalities, disequalities
    if(expose && (it->first != "=" && it->first != "distinct" && it->first[0] != '_')){
      unsigned l = (it->second).size();
      std::vector<unsigned> _temp(l);
      std::copy(it->second.begin(), it->second.end(), _temp.begin());
      for(unsigned i = 0; i < l - 1; ++i)
				for(unsigned j = i + 1; j < l; ++j)
					hC.addHornClause(cc.getEC(), cc.getVertex(_temp[i]), cc.getVertex(_temp[j]), false);
    }
    expose = false;
  }
}

void EUFInterpolant::addNegativeHornClauses(){
	std::vector<std::pair<Z3_ast, Z3_ast> > b = cc.getDisequations();
	unsigned lhs, rhs;
	Vertex * lhsVertex, * rhsVertex;
	for(std::vector<std::pair<Z3_ast, Z3_ast> >::iterator it = b.begin();
			it != b.end(); ++it){
		lhs = Z3_get_ast_id(ctx, it->first);
		rhs = Z3_get_ast_id(ctx, it->second);
		lhsVertex = cc.getVertex(cc.getVertex(lhs));
		rhsVertex = cc.getVertex(cc.getVertex(rhs));
		// It's assumed function symbol names
		// have unique arities
		if(lhsVertex->getName() == rhsVertex->getName()){
			// Add HornClauses unfolding arguments
			// Let's check anyways
			if(lhsVertex->getArity() != rhsVertex->getArity())
				std::cout << "Fatal error: Different arities from EUFInterpolant.cpp::addNegativeHornClauses" << std::endl;
		  hC.addHornClause(cc.getEC(), lhsVertex, rhsVertex, true);
		}
		else{
			// Just add HornClauses using the representative
			unsigned _sizeCC = Vertex::getTotalNumVertex();
			equality fFalse = std::make_pair(cc.getVertex(_sizeCC - 1), cc.getVertex(_sizeCC - 1));
			std::vector<equality> _antecedent;
			_antecedent.push_back(std::make_pair(lhsVertex, rhsVertex));
			hC.addHornClause(cc.getEC(), _antecedent, fFalse, true);
		}
	}
	return;
}

std::ostream & EUFInterpolant::print(std::ostream & os){
  return os;
}
