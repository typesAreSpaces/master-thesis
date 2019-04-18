#include "EUFInterpolant.h"


EUFInterpolant::EUFInterpolant(Z3_context c, Z3_ast v, Converter & cvt) :
  congruence_closure(c, v),
  cvt(cvt),
  horn_clauses(congruence_closure.getTerms()),
  ctx(c) {
  unsigned size_congruence_closure = Vertex::getTotalNumVertex();
  auto last_vertex = congruence_closure.getVertex(size_congruence_closure - 1);
  contradiction = std::make_pair(last_vertex, last_vertex);
  }

EUFInterpolant::EUFInterpolant(Z3_context c, Z3_ast v,
							   std::set<std::string> & symbols_to_elim,
							   Converter & cvt) :
  congruence_closure(c, v, symbols_to_elim),
  cvt(cvt),
  horn_clauses(congruence_closure.getTerms()),
  ctx(c) {
  unsigned size_congruence_closure = Vertex::getTotalNumVertex();
  auto last_vertex = congruence_closure.getVertex(size_congruence_closure - 1);
  contradiction = std::make_pair(last_vertex, last_vertex);
  }

EUFInterpolant::~EUFInterpolant(){
}

std::vector<HornClause*> EUFInterpolant::getHornClauses(){
  return horn_clauses.getHornClauses();
}

void EUFInterpolant::algorithm(){
  
  auto terms = congruence_closure.getTerms();
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
  // std::cout << "All Horn equations produced by the algorithm:" << std::endl;
  // std::cout << horn_clauses << std::endl;
  
  auto horn_clauses_produced = horn_clauses.getHornClauses();
  auto horn_clauses_produced_z3 = cvt.convert(horn_clauses_produced);
  
  // std::cout << "Candidate Horn equations produced: start" << std::endl;
  // unsigned l = horn_clauses_produced.size();
  // for(unsigned i = 0; i < l; ++i){
  // 	auto temp = horn_clauses_produced_z3[i];
  // 	std::cout << cvt.getAntecedent(temp) << " -> ";
  // 	std::cout << cvt.getConsequent(temp) << std::endl;
  // }
  // std::cout << "Candidate Horn equations produced: end" << std::endl;
	
  auto equations = cvt.convert(congruence_closure.getEquations());
  
  // std::cout << "Original Equations:" << std::endl;
  // for(auto equation = equations.begin();
  // 	  equation != equations.end(); ++equation){
  // 	display_ast(ctx, stdout, equation->first);
  // 	std::cout << " = ";
  // 	display_ast(ctx, stdout, equation->second);
  // 	std::cout << std::endl;
  // }

  // auto disequations = congruence_closure.getDisequations();
  // std::cout << "Original Disequations:" << std::endl;
  // for(auto disequation = disequations.begin();
  // 	  disequation != disequations.end(); ++disequation){
  // 	display_ast(ctx, stdout, disequation->first);
  // 	std::cout << " ~= ";
  // 	display_ast(ctx, stdout, disequation->second);
  // 	std::cout << std::endl;
  // }
  
  auto uncomm_terms_elim = getUncommonTermsToElim(horn_clauses_produced);
  
  // for(auto it = uncomm_terms_elim.begin();
  // 	  it != uncomm_terms_elim.end(); ++it)
  // 	std::cout << cvt.convert(terms[*it]) << std::endl;
  
  // Continue Here
  // Function exponentialElimination {
  // Input: 
  // -) equations --- (as z3::expr_vector)
  // -) uncomm_terms_elim
  //    {set of uncommon terms that I can get rid of} --- (as set of Z3_ast ids)
  // -) horn_clauses_produced_z3 --- (as z3::expr_vector)
  // }
  
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

	// std::cout << "Inside addNegativeHornClauses" << std::endl;
	// std::cout << lhs_vertex->to_string() << " ~= ";
	// std::cout << rhs_vertex->to_string() << std::endl;
	
	// It's assumed function symbol names
	// have unique arities
	if(lhs_vertex->getName() == rhs_vertex->getName()){
	  // Add HornClauses unfolding arguments
	  // Let's check anyways
	  assert(lhs_vertex->getArity() == rhs_vertex->getArity());
	  horn_clauses.addHornClause(congruence_closure.getEquivalenceClass(),
								 lhs_vertex,
								 rhs_vertex,
								 true);
	}
	else{
	  // Just add HornClauses using the representative
	  std::vector<equality> _antecedent;
	  _antecedent.push_back(std::make_pair(lhs_vertex, rhs_vertex));
	  // Add HornClauses 'directly' using the antecedent
	  // and contradiction as consequent
	  horn_clauses.addHornClause(congruence_closure.getEquivalenceClass(),
								 _antecedent,
								 contradiction,
								 true);
	}
  }
  return;
}

std::set<unsigned> EUFInterpolant::getUncommonTermsToElim(std::vector<HornClause*> & horn_clauses){
  std::set<unsigned> answer;
  for(auto horn_clause = horn_clauses.begin();
	  horn_clause != horn_clauses.end(); ++horn_clause){
	Vertex* v = (**horn_clause).getConsequent().second;
	// v is a pointer to a Vertex
	// which is only added to 'answer' if it
	// is uncommon
	if(!v->getSymbolCommonQ())
	  answer.insert(Z3_get_ast_id(ctx, cvt.convert(v)));
  }
  return answer;
}

z3::expr EUFInterpolant::exponentialElimination(z3::expr_vector & equations,
												std::set<unsigned> & terms_elim,
												z3::expr_vector & hcs){
  if(terms_elim.empty())
	return cvt.makeConjunction(equations);
  else{
	auto element = terms_elim.begin();
	terms_elim.erase(element);
	//z3::expr_vector new_equations(ctx);
	auto new_equations = equations;
	return exponentialElimination(new_equations, terms_elim, hcs);
  }
}

std::set<z3::expr> EUFInterpolant::substitutions(z3::expr & formula,
												 z3::expr & term,
												 z3::expr_vector & hcs){
  std::set<z3::expr> answer;
  unsigned hcs_length = hcs.size();
  for(unsigned i = 0; i < hcs_length; ++i){
	// current_hc_term is the 'y' in the Horn
	// clause 'antecedent -> x = y'
	auto current_hc_term = hcs[i].arg(1).arg(1);
	if(cvt.areEqual(term, current_hc_term)){
	  std::cout << "Ok lol" << std::endl;
	}
  }
  return answer;
}

// Not implemented yet!
std::ostream & operator << (std::ostream & os, EUFInterpolant & euf){
  return os;
}
