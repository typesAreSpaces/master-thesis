#include "EUFInterpolant.h"

EUFInterpolant::EUFInterpolant(Z3_context c, Z3_ast v) :
  cc(c, v), horn_clauses(cc.getTerms()), ctx(c) {
}

EUFInterpolant::EUFInterpolant(Z3_context c, Z3_ast v, std::set<std::string> & symbolsToElim) :
  cc(c, v, symbolsToElim), horn_clauses(cc.getTerms()), ctx(c) {
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
  horn_clauses.conditionalElimination();

	std::cout << horn_clauses << std::endl;
	
	std::vector<HornClause*> hCS = horn_clauses.getHornClauses();
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
  std::set<std::string> & symbols_to_eliminate = cc.getSymbolsToElim();
  
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
      std::string root_name = root->getName();
      symbol_locations[root_name].insert(root->getId());
      bool is_root_eliminable = (symbols_to_eliminate.find(root_name)
											 == symbols_to_eliminate.end()) ? true : false;
      std::vector<Vertex*> root_successors = root->getSuccessors();
      for(unsigned i = 0; i < _arity; ++i){
				if(!is_root_eliminable)
					break;
				is_root_eliminable = is_root_eliminable
					&& root_successors[i]->getSymbolCommonQ();
      }
      root->setSymbolCommonQ(is_root_eliminable);
      root = nullptr;
    }
  } while(!s.empty());
}

void EUFInterpolant::setCommonRepresentatives(){
  unsigned totalNV = Vertex::getTotalNumVertex();
  for(unsigned i = 0; i < totalNV; ++i){
    Vertex * vertex_iterator = cc.getOriginalVertex(i);
    // A rotation between the current 
    // representative and the current term if:
    // 1) the current term is common
    // 2) the current term has a smaller arity
    if(vertex_iterator->getSymbolCommonQ()
       && vertex_iterator->getArity() < cc.getVertex(vertex_iterator)->getArity()){
      cc.rotate(vertex_iterator, cc.getVertex(vertex_iterator));
		}
  }
}

void EUFInterpolant::eliminationOfUncommonFSyms(){
  bool expose = false;
  for(symbolLocations::iterator it = symbol_locations.begin();
      it != symbol_locations.end(); ++it){
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
				for(unsigned j = i + 1; j < l; ++j){
					horn_clauses.addHornClause(cc.getEC(), cc.getVertex(_temp[i]), cc.getVertex(_temp[j]), false);
				}
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
		  horn_clauses.addHornClause(cc.getEC(), lhsVertex, rhsVertex, true);
		}
		else{
			// Just add HornClauses using the representative
			unsigned _sizeCC = Vertex::getTotalNumVertex();
			equality fFalse = std::make_pair(cc.getVertex(_sizeCC - 1), cc.getVertex(_sizeCC - 1));
			std::vector<equality> _antecedent;
			_antecedent.push_back(std::make_pair(lhsVertex, rhsVertex));
			horn_clauses.addHornClause(cc.getEC(), _antecedent, fFalse, true);
		}
	}
	return;
}

std::ostream & EUFInterpolant::print(std::ostream & os){
  return os;
}
