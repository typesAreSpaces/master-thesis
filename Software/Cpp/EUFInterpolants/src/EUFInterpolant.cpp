#include "EUFInterpolant.h"
#define DEBUG_EUFINTERPOLANT false

typedef std::pair<Term*, Term*> EquationTerm;

EUFInterpolant::EUFInterpolant(const z3::expr & e, const z3::sort & s) :
  auxiliar_closure(e.ctx(), e),
  original_closure(e.ctx(), e),
  cvt(e.ctx(), s),
  horn_clauses(original_closure, auxiliar_closure),
  contradiction(original_closure.getOriginalTerm(0), original_closure.getOriginalTerm(0))
{
}

EUFInterpolant::EUFInterpolant(const z3::expr & e, const UncommonSymbols & symbols_to_elim, const z3::sort & s) :
  auxiliar_closure(e.ctx(), e, symbols_to_elim),
  original_closure(e.ctx(), e, symbols_to_elim),
  cvt(e.ctx(), s),
  horn_clauses(original_closure, auxiliar_closure),
  contradiction(original_closure.getOriginalTerm(0), original_closure.getOriginalTerm(0))
{
}

EUFInterpolant::~EUFInterpolant(){
}

z3::expr EUFInterpolant::buildInterpolant(){
  eliminationOfUncommonFSyms();
  addNegativeHornClauses();
  horn_clauses.conditionalElimination();
  
  auto non_reducible_hs_z3 = cvt.convert(horn_clauses.getHornClauses());
  auto simplified_hs = cvt.extraSimplification(non_reducible_hs_z3);
  
  auto reducible_hs = horn_clauses.getReducibleHornClauses();
  auto reducible_hs_z3 = cvt.convert(reducible_hs);
  
  auto equations = cvt.convert(original_closure.getEquations());
  auto uncomm_terms_elim = getUncommonTermsToElim(reducible_hs);
  
  auto exponential_hs = exponentialElimination(equations, uncomm_terms_elim, reducible_hs_z3);
  auto simplified_exponential_hs = cvt.extraSimplification(exponential_hs);
  auto common_simplified_exponential_hs = cvt.removeUncommonTerms(simplified_exponential_hs);
  
  return cvt.makeConjunction(simplified_hs) && cvt.makeConjunction(common_simplified_exponential_hs);
}

std::vector<HornClause*> EUFInterpolant::getHornClauses(){
  return horn_clauses.getHornClauses();
}

// If a symbol is the symbol name of an uncommon
// term then we expose the arguments of all the
// terms (locations) that contain such symbol
void EUFInterpolant::eliminationOfUncommonFSyms(){
  for(auto map_iterator : original_closure.getSymbolLocations()){
    auto symbol_name = map_iterator.first;
    // We don't include in the Exposure method new introduced symbols
    // nor equalities, disequalities, nor the initial conjuction
    if(symbol_name[0] != '=' && symbol_name != "distinct"
       && symbol_name != "and" && symbol_name[0] != '_'){
      auto locations = map_iterator.second;
      
      bool expose = false;
      for(auto location : locations)
	if(!original_closure.getReprTerm(location)->getSymbolCommonQ()){
	  expose = true;
	  break;
	}
      
      if(expose){
	unsigned number_of_locations = locations.size();
	for(unsigned location_i = 0; location_i < number_of_locations - 1; ++location_i)
	  for(unsigned location_j = location_i + 1; location_j < number_of_locations; ++location_j)
	    // Exposing two terms that have the same symbol name
	    if(locations[location_i] != locations[location_j])
	      horn_clauses.addHornClause(auxiliar_closure.getOriginalTerm(locations[location_i]),
					 auxiliar_closure.getOriginalTerm(locations[location_j]),
					 false);
	  
      }
    }
  }
}

void EUFInterpolant::addNegativeHornClauses(){
  auto disequations = original_closure.getDisequations();
  Term * lhs, * rhs;
  
  for(auto disequation : disequations){
	
    lhs = auxiliar_closure.getOriginalTerm(disequation.first.id());
    rhs = auxiliar_closure.getOriginalTerm(disequation.second.id());

    // Add HornClauses unfolding arguments
    if(lhs->getName() == rhs->getName()){
      assert(lhs->getArity() == rhs->getArity());
      horn_clauses.addHornClause(lhs, rhs, true);
    }
    else{
      // Just add HornClauses using the representative
      std::vector<EquationTerm> antecedent;
      antecedent.push_back(std::make_pair(lhs, rhs));
      // Add HornClauses 'directly' using the antecedent
      // and contradiction as consequent
      horn_clauses.addHornClause(antecedent, contradiction, true); // Needs testing
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
    if(!v->getSymbolCommonQ())
      answer.push_back(cvt.convert(v));
  }
  return answer;
}

z3::expr_vector EUFInterpolant::exponentialElimination(z3::expr_vector & equations,
						       z3::expr_vector & terms_elim,
						       z3::expr_vector & hcs){
  z3::expr_vector new_equations(equations.ctx());
  for(auto term_elim : terms_elim){
    
    new_equations.resize(0);

    for(auto equation : equations){
      // Remark: substitutions can produce horn clauses!
      // so new_equations are not all equations!
      // std::cout << "------------------------------------------------" << std::endl;
      for(auto substitution : substitutions(equation, term_elim, hcs)){
	// std::cout << substitution << std::endl;
	new_equations.push_back(substitution);
      }
    }

    equations.resize(0);
    
    // Deep - copy
    for(auto equation : new_equations) 
      equations.push_back(equation);
  }
  return equations;
}


z3::expr_vector EUFInterpolant::substitutions(z3::expr & equation,
					      z3::expr & term_elim,
					      z3::expr_vector & hcs){
  z3::expr_vector answer(equation.ctx()), from(equation.ctx()), to(equation.ctx());
  from.push_back(term_elim);
  unsigned hcs_length = hcs.size();
  std::set<unsigned> expr_ids;
  
  for(unsigned index_hc = 0; index_hc < hcs_length; ++index_hc){
    auto current_consequent_lhs = hcs[index_hc].arg(1).arg(0);
    auto current_consequent_rhs = hcs[index_hc].arg(1).arg(1);
    auto antecedent = hcs[index_hc].arg(0);
    if(cvt.areEqual(term_elim, current_consequent_rhs)){
      to.push_back(current_consequent_lhs);
      auto new_equation = equation.substitute(from, to);
      
      // Only commit to do the substitution
      // if these formulas are different
      if(new_equation.id() != equation.id()){
	if(new_equation.is_implies())
	  answer.push_back(implies(antecedent && new_equation.arg(0), new_equation.arg(1)));
	else
	  answer.push_back(implies(antecedent, new_equation));
      }
      else{
	if(notInSet(new_equation.id(), expr_ids)){
	  answer.push_back(new_equation);
	  expr_ids.insert(new_equation.id());
	}
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
