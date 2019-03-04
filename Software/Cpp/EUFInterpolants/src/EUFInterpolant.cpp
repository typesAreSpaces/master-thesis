#include "EUFInterpolant.h"

EUFInterpolant::EUFInterpolant(Z3_context c, Z3_ast v) :
  congruence_closure(c, v),
	horn_clauses(congruence_closure.getTerms()),
	ctx(c) {
}

EUFInterpolant::EUFInterpolant(Z3_context c, Z3_ast v,
															 std::set<std::string> & symbols_to_elim) :
  congruence_closure(c, v, symbols_to_elim),
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
  eliminationOfUncommonFSyms();
	addNegativeHornClauses();

	// ------------------------------------
	// TODO: FIX THIS!
	// UPDATE: IT LOOKS LIKE IT'S DONE!
  horn_clauses.conditionalElimination();
	// ------------------------------------
	//std::cout << horn_clauses << std::endl;
	
	auto hCS = horn_clauses.getHornClauses();
	std::cout << "Horn equations produced:" << std::endl;
	for(auto it = hCS.begin();
			it != hCS.end(); ++it){
		std::cout << **it << std::endl;
	}
	
	std::cout << "Original Equations:" << std::endl;
	auto equations = congruence_closure.getEquations();
	for(auto equation = equations.begin();
			equation != equations.end(); ++equation){
	  display_ast(ctx, stdout, equation->first);
		std::cout << " = ";
		display_ast(ctx, stdout, equation->second);
		std::cout << std::endl;
	}

	std::cout << "Original Disequations:" << std::endl;
	auto disequations = congruence_closure.getDisequations();
	for(auto disequation = disequations.begin();
			disequation != disequations.end(); ++disequation){
		display_ast(ctx, stdout, disequation->first);
		std::cout << " ~= ";
		display_ast(ctx, stdout, disequation->second);
		std::cout << std::endl;
	}

	// Continue Here
	
}

void EUFInterpolant::identifyCommonSymbols(){
  unsigned root_num = congruence_closure.getRootNum();
  std::stack<Vertex*> stack_vertices;
  Vertex * root = congruence_closure.getVertex(root_num), * temp_root;
  unsigned arity;
  auto & symbols_to_eliminate = congruence_closure.getSymbolsToElim();
  
  // Traversing the graph (in post-order) 
  // to determine if a term is common or not
  do{
    while(root != nullptr){
      arity = root->getArity();
      switch(arity){
      case 0:
				stack_vertices.push(root);
				root = nullptr;
				break;
      case 1:
				stack_vertices.push(root);
				root = root->getLeftChild();
				break;
      case 2:
				stack_vertices.push(root->getRightChild()), stack_vertices.push(root);
				root = root->getLeftChild();
				break;
      default:
				break;
      }
    } 
    root = stack_vertices.top(), stack_vertices.pop();
    arity = root->getArity();
    if(arity == 2 && !stack_vertices.empty()
       && root->getRightChild()->getId() == stack_vertices.top()->getId()){
      temp_root = stack_vertices.top();
      stack_vertices.pop();
      stack_vertices.push(root);
      root = temp_root;
    }
    else{
      // do something with root
      std::string root_name = root->getName();
      symbol_locations[root_name].insert(root->getId());
      bool is_root_eliminable = (symbols_to_eliminate.find(root_name)
											 == symbols_to_eliminate.end()) ? true : false;
      std::vector<Vertex*> root_successors = root->getSuccessors();
      for(unsigned i = 0; i < arity; ++i){
				if(!is_root_eliminable)
					break;
				is_root_eliminable = is_root_eliminable
					&& root_successors[i]->getSymbolCommonQ();
      }
      root->setSymbolCommonQ(is_root_eliminable);
      root = nullptr;
    }
  } while(!stack_vertices.empty());
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
	
  for(auto map_symbol_location = symbol_locations.begin();
      map_symbol_location != symbol_locations.end(); ++map_symbol_location){
		auto symbol_name = map_symbol_location->first;
		auto positions = map_symbol_location->second;
    for(auto position : positions){
      if(!congruence_closure.getVertex(position)->getSymbolCommonQ()){
				expose = true;
				break;
      }
    }
		
		// We don't include in the Exposure method new introduced symbols
		// nor equalities, disequalities
    if(expose && (symbol_name[0] != '=' &&
									symbol_name != "distinct" &&
									symbol_name[0] != '_')){
      unsigned number_of_positions = positions.size();
			// Why: do I need a new vector _temp?
      std::vector<unsigned> _temp(number_of_positions);
      std::copy(positions.begin(), positions.end(), _temp.begin());
      for(unsigned i = 0; i < number_of_positions - 1; ++i)
				for(unsigned j = i + 1; j < number_of_positions; ++j){
					horn_clauses.addHornClause(congruence_closure.getEquivalenceClass(),
																		 congruence_closure.getOriginalVertex(_temp[i]),
																		 congruence_closure.getOriginalVertex(_temp[j]),
																		 false);
				}
    }
    expose = false;
  }
}

void EUFInterpolant::addNegativeHornClauses(){
  auto disequations = congruence_closure.getDisequations();
	unsigned lhs, rhs;
	Vertex * lhs_vertex, * rhs_vertex;
	for(auto disequation = disequations.begin();
			disequation != disequations.end(); ++disequation){
		lhs = Z3_get_ast_id(ctx, disequation->first);
		rhs = Z3_get_ast_id(ctx, disequation->second);
		lhs_vertex = congruence_closure.getVertex(lhs);
		rhs_vertex = congruence_closure.getVertex(rhs);
		// It's assumed function symbol names
		// have unique arities
		if(lhs_vertex->getName() == rhs_vertex->getName()){
			// Add HornClauses unfolding arguments
			// Let's check anyways
			assert(lhs_vertex->getArity() != rhs_vertex->getArity());
		  horn_clauses.addHornClause(congruence_closure.getEquivalenceClass(),
																 lhs_vertex,
																 rhs_vertex,
																 true);
		}
		else{
			// Just add HornClauses using the representative
			unsigned _sizeCC = Vertex::getTotalNumVertex();
			equality fFalse = std::make_pair(congruence_closure.getVertex(_sizeCC - 1),
																			 congruence_closure.getVertex(_sizeCC - 1));
			std::vector<equality> _antecedent;
			_antecedent.push_back(std::make_pair(lhs_vertex, rhs_vertex));
			horn_clauses.addHornClause(congruence_closure.getEquivalenceClass(),
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
