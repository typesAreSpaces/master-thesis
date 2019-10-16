#include "EUFInterpolant.h"
#define DEBUG_EUFINTERPOLANT false

typedef std::pair<Term*, Term*> EquationTerm;

EUFInterpolant::EUFInterpolant(const z3::expr & e, const z3::sort & s) :
  auxiliar_closure(e.ctx(), e, 0),
  original_closure(e.ctx(), e, 1),
  cvt(e.ctx(), s),
  horn_clauses(original_closure, auxiliar_closure),
  contradiction(original_closure.getOriginalTerm(0),
		original_closure.getOriginalTerm(0)){
}

EUFInterpolant::EUFInterpolant(const z3::expr & e,
			       const UncommonSymbols & symbols_to_elim,
			       const z3::sort & s) :
  auxiliar_closure(e.ctx(), e, symbols_to_elim, 0),
  original_closure(e.ctx(), e, symbols_to_elim, 1),
  cvt(e.ctx(), s),
  horn_clauses(original_closure, auxiliar_closure),
  contradiction(original_closure.getOriginalTerm(0),
		original_closure.getOriginalTerm(0)){
}

EUFInterpolant::~EUFInterpolant(){
}

void EUFInterpolant::test(){
  setCommonRepresentatives();
  eliminationOfUncommonFSyms();// TODO
  return;
}

z3::expr EUFInterpolant::buildInterpolant(){
  setCommonRepresentatives(); // Check
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
  
  auto equations = cvt.convert(original_closure.getEquations());
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

void EUFInterpolant::setCommonRepresentatives(){
#if DEBUG_EUFINTERPOLANT
  for(auto term : original_closure.getTerms())
    std::cout << "Original: " << term->to_string() << std::endl
	      << "Repr: " << original_closure.getReprTerm(term)->to_string()
	      << std::endl << std::endl;
#endif
  for(auto term : original_closure.getTerms()){
    Term * term_repr = original_closure.getReprTerm(term);
    // A rotation between the current 
    // representative and the current term if:
    // 1) the current term is common
    // 2) the current term has a smaller arity
    if(term->getSymbolCommonQ() && term->getArity() < term_repr->getArity()){
      original_closure.rotate(term, term_repr);
#if DEBUG_EUFINTERPOLANT
      std::cout << "A rotation occurred between " << std::endl
		<< "-> " << *term << std::endl
		<< "and\n"
		<< "-> " << *term_repr << std::endl;
#endif
    }
  }

#if DEBUG_EUFINTERPOLANT
  for(auto term : original_closure.getTerms())
    std::cout << "Original: " << term->to_string() << std::endl
	      << "Repr: " << original_closure.getReprTerm(term)->to_string()
	      << std::endl << std::endl;
#endif
}

// If a symbol is the symbol name of an uncommon
// term then we expose the arguments of all the
// terms (locations) that contain such symbol
void EUFInterpolant::eliminationOfUncommonFSyms(){
  for(auto map_iterator : original_closure.getSymbolLocations()){
    auto symbol_name = map_iterator.first;
    // We don't include in the Exposure method new introduced symbols
    // nor equalities, disequalities
    // TODO: There is a potential problem by not including the auxilar
    // symbols i.e. the ones starting with "_"
    if(symbol_name[0] != '='
       && symbol_name != "distinct"
       && symbol_name[0] != '_'){
      auto locations = map_iterator.second;
      
      bool expose = false;
      for(auto location : locations)
	if(!original_closure.getReprTerm(location)->getSymbolCommonQ()){
	  expose = true;
	  break;
	}
      
      if(expose){
	unsigned number_of_locations = locations.size();
	for(unsigned location_i = 0;
	    location_i < number_of_locations - 1;
	    ++location_i){
	  for(unsigned location_j = location_i + 1;
	      location_j < number_of_locations;
	      ++location_j){
	    // Exposing two terms that have the same symbol name
	    std::cout << location_i << " " << location_j << std::endl;
	    if(locations[location_i] != locations[location_j])
	      horn_clauses.addHornClause(auxiliar_closure.getOriginalTerm(locations[location_i]),
					 auxiliar_closure.getOriginalTerm(locations[location_j]),
					 false);
	  }
	} 
      }
    }
  }
}

void EUFInterpolant::addNegativeHornClauses(){
  auto disequations = original_closure.getDisequations();
  unsigned lhs, rhs;
  Term * lhs_vertex, * rhs_vertex;
  
  for(auto disequation = disequations.begin();
      disequation != disequations.end(); ++disequation){
	
    lhs = disequation->first;
    rhs = disequation->second;
    lhs_vertex = original_closure.getReprTerm(lhs);
    rhs_vertex = original_closure.getReprTerm(rhs);

    // std::cout << "Inside addNegativeHornClauses" << std::endl;
    // std::cout << lhs_vertex->to_string() << " ~= ";
    // std::cout << rhs_vertex->to_string() << std::endl;
	
    // It's assumed function symbol names
    // have unique arities
    if(lhs_vertex->getName() == rhs_vertex->getName()){
      // Add HornClauses unfolding arguments
      // Let's check anyways
      assert(lhs_vertex->getArity() == rhs_vertex->getArity());
      horn_clauses.addHornClause(lhs_vertex,
				 rhs_vertex,
				 true); // Needds testing
    }
    else{
      // Just add HornClauses using the representative
      std::vector<EquationTerm> _antecedent;
      _antecedent.push_back(std::make_pair(lhs_vertex, rhs_vertex));
      // Add HornClauses 'directly' using the antecedent
      // and contradiction as consequent
      horn_clauses.addHornClause(_antecedent,
				 contradiction,
				 true); // Needs testing
    }
  }
  return;
}

z3::expr_vector EUFInterpolant::getUncommonTermsToElim(std::vector<HornClause*> & horn_clauses){
  z3::expr_vector answer(original_closure.getCtx());
  for(auto horn_clause : horn_clauses){
    Term* v = (*horn_clause).getConsequent().second;
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
      if(formula_subs.id() != formula.id()){
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
