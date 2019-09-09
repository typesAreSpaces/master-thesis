#include "EUFInterpolant.h"
#define DEBUGGING false
#define DEBUG_MSG(X,Y) if(X){Y}


typedef std::pair<Term*, Term*> EquationTerm;

EUFInterpolant::EUFInterpolant(const z3::expr & e, const z3::sort & s) :
  congruence_closure(e.ctx(), e),
  original_structure(e.ctx(), e),
  cvt(e.ctx(), s),
  horn_clauses(congruence_closure.getTerms()),
  contradiction(congruence_closure.getOriginalTerm(0),
		congruence_closure.getOriginalTerm(0)){
  original_structure.buildCongruenceClosure();
}

EUFInterpolant::EUFInterpolant(const z3::expr & e,
			       const std::set<std::string> & symbols_to_elim,
			       const z3::sort & s) :
  congruence_closure(e.ctx(), e, symbols_to_elim),
  original_structure(e.ctx(), e, symbols_to_elim),
  cvt(e.ctx(), s),
  horn_clauses(congruence_closure.getTerms()),
  contradiction(congruence_closure.getOriginalTerm(0),
		congruence_closure.getOriginalTerm(0)){
  original_structure.buildCongruenceClosure();
}

EUFInterpolant::~EUFInterpolant(){}

void EUFInterpolant::test(){
  identifyCommonSymbols();
  congruence_closure.buildCongruenceClosure();
  setCommonRepresentatives();
  eliminationOfUncommonFSyms();// TODO
  return;
}

z3::expr EUFInterpolant::buildInterpolant(){
  identifyCommonSymbols(); // Check
  congruence_closure.buildCongruenceClosure(); // Check
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
  Term * current_term = congruence_closure.getReprTerm(root_num), * temp_current_term;
  unsigned arity;
  auto & symbols_to_eliminate = congruence_closure.getSymbolsToElim();
  std::stack<Term*> stack_vertices;
   
  // Traversing the graph (in post-order) 
  // to determine if a term is common or not
  // Reference: https://www.geeksforgeeks.org/iterative-postorder-traversal-using-stack/
  do{
    while(current_term != nullptr){
      arity = current_term->getArity();
      switch(arity){
      case 0:
	stack_vertices.push(current_term);
	current_term = nullptr;
	break;
      case 1:
	stack_vertices.push(current_term);
	current_term = current_term->getLeftChild();
	break;
      case 2:
	stack_vertices.push(current_term->getRightChild()), stack_vertices.push(current_term);
	current_term = current_term->getLeftChild();
	break;
      default:
	throw("Error: Arity cannot be more than 2");
	break;
      }
    }
    current_term = stack_vertices.top();
    stack_vertices.pop();
    arity = current_term->getArity();
    if(arity == 2 && !stack_vertices.empty()
       && current_term->getRightChild()->getId() == stack_vertices.top()->getId()){
      temp_current_term = stack_vertices.top();
      stack_vertices.pop();
      stack_vertices.push(current_term);
      current_term = temp_current_term;
    }
    else{
      // do something with current_term
      std::string current_term_name = current_term->getName();
      symbol_locations[current_term_name].push_back(current_term->getId());
      bool is_current_term_common =
	symbols_to_eliminate.find(current_term_name) == symbols_to_eliminate.end();
      for(auto successor : current_term->getSuccessors()){
	if(!is_current_term_common)
	  break;
	is_current_term_common = successor->getSymbolCommonQ();
      }
      current_term->setSymbolCommonQ(is_current_term_common);
      current_term = nullptr;
    }
  } while(!stack_vertices.empty());
}

void EUFInterpolant::setCommonRepresentatives(){

#if DEBUGGING
  for(auto term : congruence_closure.getTerms())
    std::cout << "Original: " << term->to_string() << std::endl
	      << "Repr: " << congruence_closure.getReprTerm(term)->to_string()
	      << std::endl << std::endl;
#endif
  
  for(auto term : congruence_closure.getTerms()){
    Term * term_repr = congruence_closure.getReprTerm(term);
    // A rotation between the current 
    // representative and the current term if:
    // 1) the current term is common
    // 2) the current term has a smaller arity
    if(term->getSymbolCommonQ() && term->getArity() < term_repr->getArity()){
      congruence_closure.rotate(term, term_repr);
#if DEBUGGING
      std::cout << "A rotation occurred between " << std::endl
		<< "-> " << *term << std::endl
		<< "and\n"
		<< "-> " << *term_repr << std::endl;
#endif
    }
  }

#if DEBUGGING
  for(auto term : congruence_closure.getTerms())
    std::cout << "Original: " << term->to_string() << std::endl
	      << "Repr: " << congruence_closure.getReprTerm(term)->to_string()
	      << std::endl << std::endl;
#endif
}

void EUFInterpolant::eliminationOfUncommonFSyms(){
  bool expose = false;
	
  for(auto map_iterator : symbol_locations){
    auto symbol_name = map_iterator.first;
    auto locations = map_iterator.second;
    
    for(auto location : locations)
      if(!congruence_closure.getReprTerm(location)->getSymbolCommonQ()){
	expose = true;
	break;
      }
		
    // We don't include in the Exposure method new introduced symbols
    // nor equalities, disequalities
    if(expose && (symbol_name[0] != '=' &&
		  symbol_name != "distinct" &&
		  symbol_name[0] != '_')){
      unsigned number_of_locations = locations.size();
      std::vector<unsigned> _temp(number_of_locations);
      for(unsigned i = 0; i < number_of_locations - 1; ++i)
	for(unsigned j = i + 1; j < number_of_locations; ++j){
	  // This 
	  horn_clauses.addHornClause(congruence_closure.getEquivalenceClass(),
				     congruence_closure.getReprTerm(locations[i]),
				     congruence_closure.getReprTerm(locations[j]),
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
	
    lhs = disequation->first;
    rhs = disequation->second;
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
  z3::expr_vector answer(congruence_closure.getCtx());
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
