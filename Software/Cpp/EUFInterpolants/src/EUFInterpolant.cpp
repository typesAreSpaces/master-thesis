#include "EUFInterpolant.h"


EUFInterpolant::EUFInterpolant(z3::context & c, const z3::expr & v, Converter & cvt) :
  congruence_closure(c, v),
  cvt(cvt),
  horn_clauses(congruence_closure.getTerms()),
  ctx(c){
  contradiction = std::make_pair(congruence_closure.getOriginalTerm(0),
				 congruence_closure.getOriginalTerm(0));
  }

EUFInterpolant::EUFInterpolant(z3::context & c, const z3::expr & v,
			       std::set<std::string> & symbols_to_elim,
			       Converter & cvt) :
  congruence_closure(c, v, symbols_to_elim),
  cvt(cvt),
  horn_clauses(congruence_closure.getTerms()),
  ctx(c) {
  contradiction = std::make_pair(congruence_closure.getOriginalTerm(0),
				 congruence_closure.getOriginalTerm(0));
  }

EUFInterpolant::~EUFInterpolant(){
}

void EUFInterpolant::test(){
  return;
}

z3::expr EUFInterpolant::algorithm(){
  identifyCommonSymbols();
  congruence_closure.buildCongruenceClosure();
  setCommonRepresentatives();
  eliminationOfUncommonFSyms();
  addNegativeHornClauses();
  // ------------------------------------
  // TODO: FIX THIS!
  // UPDATE: IT LOOKS LIKE IT'S DONE!
  horn_clauses.conditionalElimination();
  // ------------------------------------
  
  auto non_reducible_hs = horn_clauses.getHornClauses();
  auto non_reducible_hs_z3 = cvt.convert(non_reducible_hs);
  auto simplified_hs = cvt.extraSimplification(non_reducible_hs_z3);
  
  std::cout << "Non Reducible" << std::endl;
  std::cout << simplified_hs << std::endl;
  
  auto reducible_hs = horn_clauses.getReducibleHornClauses();
  auto reducible_hs_z3 = cvt.convert(reducible_hs);

  std::cout << "Reducible" << std::endl;
  std::cout << reducible_hs_z3 << std::endl;
  
  auto equations = cvt.convert(congruence_closure.getEquations());
  auto uncomm_terms_elim = getUncommonTermsToElim(reducible_hs);

  std::cout << "ok" << std::endl;
  
  auto exponential_hs = exponentialElimination(equations,
					       uncomm_terms_elim,
					       reducible_hs_z3);
  std::cout << "Exponential" << std::endl;
  std::cout << exponential_hs << std::endl;
  
  auto simplified_exponential_hs = cvt.extraSimplification(exponential_hs);  
  
  return cvt.makeConjunction(simplified_hs)
    && cvt.makeConjunction(simplified_exponential_hs);
}

std::vector<HornClause*> EUFInterpolant::getHornClauses(){
  return horn_clauses.getHornClauses();
}

void EUFInterpolant::identifyCommonSymbols(){
  unsigned root_num = congruence_closure.getRootNum();
  Term * root = congruence_closure.getReprTerm(root_num), * temp_root;
  unsigned arity;
  auto & symbols_to_eliminate = congruence_closure.getSymbolsToElim();
  std::stack<Term*> stack_vertices;
  
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
      std::vector<Term*> root_successors = root->getSuccessors();
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
  unsigned totalNV = Term::getTotalNumTerm();
  for(unsigned i = 0; i < totalNV; ++i){
    Term * vertex_iterator = congruence_closure.getOriginalTerm(i);
    Term * vertex_representative = congruence_closure.getReprTerm(vertex_iterator);
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
      if(!congruence_closure.getReprTerm(position)->getSymbolCommonQ()){
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
				     congruence_closure.getOriginalTerm(_temp[i]),
				     congruence_closure.getOriginalTerm(_temp[j]),
				     false);
	}
    }
    expose = false;
  }
}

void EUFInterpolant::addNegativeHornClauses(){
  auto disequations = congruence_closure.getDisequations();
  unsigned lhs, rhs;
  Term * lhs_vertex, * rhs_vertex;
  
  for(auto disequation = disequations.begin();
      disequation != disequations.end(); ++disequation){
	
    lhs = Z3_get_ast_id(ctx, disequation->first);
    rhs = Z3_get_ast_id(ctx, disequation->second);
    lhs_vertex = congruence_closure.getReprTerm(lhs);
    rhs_vertex = congruence_closure.getReprTerm(rhs);

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
      std::vector<EquationTerm> _antecedent;
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

z3::expr_vector EUFInterpolant::getUncommonTermsToElim(std::vector<HornClause*> & horn_clauses){
  z3::expr_vector answer(ctx);
  for(auto horn_clause = horn_clauses.begin();
      horn_clause != horn_clauses.end(); ++horn_clause){
    Term* v = (**horn_clause).getConsequent().second;
    // v is a pointer to a Term
    // which is only added to 'answer' if it
    // is uncommon
    if(!v->getSymbolCommonQ()){
      // auto new_expr = cvt.convert(v);
      // std::cout << "Expression" << std::endl;
      // std::cout << v->getId() << std::endl;
      // std::cout << "New expression converted" << std::endl;
      // std::cout << new_expr << std::endl;
      // std::cout << Z3_get_ast_id(ctx, new_expr) << std::endl;
      // answer.insert(Z3_get_ast_id(ctx, new_expr));
      // // answer.insert(v->getId());
      answer.push_back(cvt.convert(v));
    }
  }
  return answer;
}

z3::expr_vector EUFInterpolant::exponentialElimination(z3::expr_vector & equations,
						       z3::expr_vector & terms_elim,
						       z3::expr_vector & hcs){
  z3::expr_vector new_equations(equations.ctx());
  for(auto term_to_elim : terms_elim){
    new_equations.resize(0);
    for(auto equation : equations){
      auto current_substitutions = substitutions(equation, term_to_elim, hcs);
      for(auto substitution : current_substitutions)
	new_equations.push_back(substitution);
    }
    equations.resize(0);
    // Deep - copy
    for(auto substitution : new_equations)
      equations.push_back(substitution);
  }
  return equations;
}

z3::expr_vector EUFInterpolant::substitutions(z3::expr & formula,
					      z3::expr & term,
					      z3::expr_vector & hcs){
  z3::expr_vector answer(formula.ctx());
  z3::expr_vector from(formula.ctx()), to(formula.ctx());
  from.push_back(term);
  unsigned hcs_length = hcs.size();
  for(unsigned i = 0; i < hcs_length; ++i){
    // current_hc_term is the 'y' in the Horn
    // clause 'antecedent -> x = y'
    auto current_consequent_rhs = hcs[i].arg(1).arg(1);
    auto current_consequent_lhs = hcs[i].arg(1).arg(0);
    auto antecedent = hcs[i].arg(0);
    if(cvt.areEqual(term, current_consequent_rhs)){
      to.push_back(current_consequent_lhs);
      auto formula_subs = formula.substitute(from, to);
      // Only commit to do the substituion
      // if these formulas are fundamentally different
      if(Z3_get_ast_id(ctx, formula_subs) != Z3_get_ast_id(ctx, formula)){
	if(formula_subs.is_implies())
	  answer.push_back(implies(antecedent && formula_subs.arg(0),
				   formula_subs.arg(1)));
	else
	  answer.push_back(implies(antecedent, formula_subs));
      }
      to.pop_back();
    }
  }
  return answer;
}

// Not implemented yet!
std::ostream & operator << (std::ostream & os, EUFInterpolant & euf){
  return os;
}
