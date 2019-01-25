#include "EUFInterpolant.h"

EUFInterpolant::EUFInterpolant(Z3_context c, Z3_ast v) :
  congruence_closure(c, v),
	horn_clauses(congruence_closure.getTerms()),
	ctx(c) {
}

EUFInterpolant::EUFInterpolant(Z3_context c, Z3_ast v,
															 std::set<std::string> & symbolsToElim) :
  congruence_closure(c, v, symbolsToElim),
	horn_clauses(congruence_closure.getTerms()),
	ctx(c) {
}

EUFInterpolant::~EUFInterpolant(){
}

void EUFInterpolant::algorithm(){
  identifyCommonSymbols();
	// Congruence Closure Algorithm
  congruence_closure.algorithm();
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
	auto a = congruence_closure.getEquations();
	for(auto it = a.begin();
			it != a.end(); ++it){
	  display_ast(ctx, stdout, it->first);
		std::cout << " = ";
		display_ast(ctx, stdout, it->second);
		std::cout << std::endl;
	}

	std::cout << "Original Disequations:" << std::endl;
	auto b = congruence_closure.getDisequations();
	for(auto it = b.begin();
			it != b.end(); ++it){
		display_ast(ctx, stdout, it->first);
		std::cout << " ~= ";
		display_ast(ctx, stdout, it->second);
		std::cout << std::endl;
	}

	// Continue Here
	
}

void EUFInterpolant::identifyCommonSymbols(){
  unsigned rootNum = congruence_closure.getRootNum();
  std::stack<Vertex*> s;
  Vertex * root = congruence_closure.getVertex(rootNum), * _tempRoot;
  unsigned _arity;
  auto & symbols_to_eliminate = congruence_closure.getSymbolsToElim();
  
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
    Vertex * vertex_iterator = congruence_closure.getOriginalVertex(i);
		Vertex * vertex_representative = congruence_closure.getVertex(vertex_iterator);
    // A rotation between the current 
    // representative and the current term if:
    // 1) the current term is common
    // 2) the current term has a smaller arity
    if(vertex_iterator->getSymbolCommonQ()
       && vertex_iterator->getArity() < vertex_representative->getArity()){
      congruence_closure.rotate(vertex_iterator, vertex_representative);
		}
  }
}

void EUFInterpolant::eliminationOfUncommonFSyms(){
  bool expose = false;
  for(auto it = symbol_locations.begin();
      it != symbol_locations.end(); ++it){
    for(auto it2 = it->second.begin();
				it2 != it->second.end(); ++it2){
      if(!congruence_closure.getVertex(*it2)->getSymbolCommonQ()){
				expose = true;
				break;
      }
    }
		// We don't include in the Exposure method new introduced symbols
		// nor equalities, disequalities
    if(expose && (it->first != "=" &&
									it->first != "distinct" && it->first[0] != '_')){
      unsigned l = (it->second).size();
      std::vector<unsigned> _temp(l);
      std::copy(it->second.begin(), it->second.end(), _temp.begin());
      for(unsigned i = 0; i < l - 1; ++i)
				for(unsigned j = i + 1; j < l; ++j){
					horn_clauses.addHornClause(congruence_closure.getEC(),
																		 congruence_closure.getVertex(_temp[i]),
																		 congruence_closure.getVertex(_temp[j]),
																		 false);
				}
    }
    expose = false;
  }
}

void EUFInterpolant::addNegativeHornClauses(){
  auto b = congruence_closure.getDisequations();
	unsigned lhs, rhs;
	Vertex * lhsVertex, * rhsVertex;
	for(auto it = b.begin();
			it != b.end(); ++it){
		lhs = Z3_get_ast_id(ctx, it->first);
		rhs = Z3_get_ast_id(ctx, it->second);
		lhsVertex = congruence_closure.getVertex(congruence_closure.getVertex(lhs));
		rhsVertex = congruence_closure.getVertex(congruence_closure.getVertex(rhs));
		// It's assumed function symbol names
		// have unique arities
		if(lhsVertex->getName() == rhsVertex->getName()){
			// Add HornClauses unfolding arguments
			// Let's check anyways
			if(lhsVertex->getArity() != rhsVertex->getArity())
				std::cout << "Fatal error: Different arities from EUFInterpolant.cpp::addNegativeHornClauses" << std::endl;
		  horn_clauses.addHornClause(congruence_closure.getEC(),
																 lhsVertex,
																 rhsVertex,
																 true);
		}
		else{
			// Just add HornClauses using the representative
			unsigned _sizeCC = Vertex::getTotalNumVertex();
			equality fFalse = std::make_pair(congruence_closure.getVertex(_sizeCC - 1),
																			 congruence_closure.getVertex(_sizeCC - 1));
			std::vector<equality> _antecedent;
			_antecedent.push_back(std::make_pair(lhsVertex, rhsVertex));
			horn_clauses.addHornClause(congruence_closure.getEC(),
																 _antecedent,
																 fFalse,
																 true);
		}
	}
	return;
}

// Not implemented yet!
std::ostream & operator << (std::ostream & os, EUFInterpolant & euf){
  return os;
}
