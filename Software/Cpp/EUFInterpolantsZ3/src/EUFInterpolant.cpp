#include "EUFInterpolant.h"
#define DEBUG_EUFINTERPOLANT false

EUFInterpolant::EUFInterpolant(z3::expr const & part_a) :
  horn_clauses(), subterms(part_a.ctx()) {
  init(part_a);
  // eliminationOfUncommonFSyms();
}


EUFInterpolant::~EUFInterpolant(){
}

void EUFInterpolant::buildInterpolant(){
  eliminationOfUncommonFSyms();
  // horn_clauses.conditionalElimination();
  
  // auto non_reducible_hs_z3 = cvt.convert(horn_clauses.getHornClauses());
  // auto simplified_hs = cvt.extraSimplification(non_reducible_hs_z3);  
  // auto reducible_hs = horn_clauses.getReducibleHornClauses();
  // auto reducible_hs_z3 = cvt.convert(reducible_hs);
  // auto equations = cvt.convert(original_closure.getEquations());
  // auto uncomm_terms_elim = getUncommonTermsToElim(reducible_hs); // (???) but... ------------------
  // auto exponential_hs = exponentialElimination(equations, uncomm_terms_elim, reducible_hs_z3); <--|
  // auto simplified_exponential_hs = cvt.extraSimplification(exponential_hs);  
  
  // return cvt.makeConjunction(simplified_hs) && cvt.makeConjunction(simplified_exponential_hs);
  return;
}


void EUFInterpolant::init(z3::expr const & e){
  if(e.is_app()){
    if(visited.size() <= e.id()){
      visited.resize(e.id() + 1, false);
      subterms.resize(e.id() + 1);
    }
    if(visited[e.id()])
      return;
    
    visited[e.id()] = true;
    subterms.set(e.id(), (z3::expr&) e);
    
    unsigned num = e.num_args();
    for(unsigned i = 0; i < num; i++)
      init(e.arg(i));

    z3::func_decl f = e.decl();
    switch(f.decl_kind()){
    case Z3_OP_DISTINCT:{
      // TODO:
      // Take the lhs (x) and rhs (y) and produce the Horn Clause
      // repr(x) = repr(y) -> false
      return;
    }
    case Z3_OP_UNINTERPRETED:
      if(num > 0 && !e.is_common())
	uncommon_positions[f.name().str()].push_back(e.id());
    default:
      return;
    }
  }
  throw "Problem @ EUFInterpolant::init. The expression e is not an application term.";
}

void EUFInterpolant::eliminationOfUncommonFSyms(){
  for(auto iterator : uncommon_positions){
    unsigned current_num_uncomms = iterator.second.size();
    for(unsigned index_1 = 0; index_1 < current_num_uncomms - 1; index_1++)
      for(unsigned index_2 = index_1 + 1; index_2 < current_num_uncomms; index_2++){
	// TODO:
	std::cout << "Create Horn clauses for this pair" << std::endl;
	std::cout << "1. " << subterms[iterator.second[index_1]] << std::endl;
	std::cout << "2. " << subterms[iterator.second[index_2]] << std::endl;
      }
  }
}

// z3::expr_vector EUFInterpolant::getUncommonTermsToElim(std::vector<HornClause*> & horn_clauses){
//   z3::expr_vector answer(original_closure.getCtx());
//   for(auto horn_clause : horn_clauses){
//     auto v = (*horn_clause).getConsequent();
//     // v is a pointer to a Term
//     // which is only added to 'answer' if it
//     // is uncommon
//     if(!(v.first)->getSymbolCommonQ())
//       answer.push_back(cvt.convert(v.first));
    
//     if(!(v.second)->getSymbolCommonQ())
//       answer.push_back(cvt.convert(v.second));
//   }
//   return answer;
// }

// z3::expr_vector EUFInterpolant::exponentialElimination(z3::expr_vector & equations,
// 						       z3::expr_vector & terms_elim,
// 						       z3::expr_vector & hcs){
//   z3::expr_vector new_equations(equations.ctx());
//   z3::expr_vector solution(equations.ctx());
//   std::map<unsigned, unsigned> num_uncomms;
//   std::set<std::string> symbols_to_elim = original_closure.getSymbolsToElim();
  
//   if(terms_elim.size() > 0)
//     for(auto term_elim : terms_elim) {

//       new_equations.resize(0);
      
//       for(auto equation : equations){

// 	unsigned num_uncomms = 0;
// 	for(auto symbol : cvt.getSymbols(equation))
// 	  if(!(notInSet(symbol, symbols_to_elim)))
// 	    ++num_uncomms;
	
// 	if(num_uncomms == 0)
// 	  solution.push_back(equation);
// 	else{
// 	  if(num_uncomms > 0)
// 	    // Remark: substitutions can produce horn clauses!
// 	    // so new_equations are not all equations!
// 	    for(auto substitution : substitutions(equation, term_elim, hcs))
// 	      new_equations.push_back(substitution);
// 	  else
// 	    throw "Expressions cannot have negative number of uncommon symbols!";
// 	}
//       }
//       equations.resize(0);
//       // Deep - copy
//       for(auto equation : new_equations) 
// 	equations.push_back(equation);
//     }
//   else
//     for(auto equation : equations){

//       unsigned num_uncomms = 0;
//       for(auto symbol : cvt.getSymbols(equation))
// 	if(!(notInSet(symbol, symbols_to_elim)))
// 	  ++num_uncomms;
      
//       if(num_uncomms == 0)
// 	solution.push_back(equation);
//     }
//   return solution;
// }


// z3::expr_vector EUFInterpolant::substitutions(z3::expr & equation,
// 					      z3::expr & term_elim,
// 					      z3::expr_vector & hcs){
//   z3::expr_vector answer(equation.ctx()), from(equation.ctx()), to(equation.ctx());
//   from.push_back(term_elim);
//   unsigned hcs_length = hcs.size();
//   std::set<unsigned> expr_ids;
  
//   for(unsigned index_hc = 0; index_hc < hcs_length; ++index_hc){
//     auto current_consequent_lhs = hcs[index_hc].arg(1).arg(0);
//     auto current_consequent_rhs = hcs[index_hc].arg(1).arg(1);
//     auto antecedent = hcs[index_hc].arg(0);
    
//     if((term_elim.id() == current_consequent_rhs.id())){
//       to.push_back(current_consequent_lhs);
//       auto new_equation = equation.substitute(from, to);
//       // If these formulas are different commit to do the substitution
//       if(new_equation.id() != equation.id()){
// 	if(new_equation.is_implies())
// 	  answer.push_back(implies(antecedent && new_equation.arg(0), new_equation.arg(1)));
// 	else
// 	  answer.push_back(implies(antecedent, new_equation));
//       }
//       else
// 	if(notInSet(new_equation.id(), expr_ids)){
// 	  answer.push_back(new_equation);
// 	  expr_ids.insert(new_equation.id());
// 	}
//       to.pop_back();
//     }
//   }
//   return answer;
// }

std::ostream & operator << (std::ostream & os, const EUFInterpolant & euf){
  unsigned num = euf.subterms.size();
  std::cout << "All the subterms:" << std::endl;
  for(unsigned i = 0; i < num; i++){
    if(euf.visited[i])
      std::cout << euf.subterms[i] << std::endl;
  }
  std::cout << "All uncommon terms:" << std::endl;
  for(auto x : euf.uncommon_positions){
    std::cout << "For (" << x.first << "):" << std::endl;
    for(auto y : x.second)
      std::cout << y << " " << euf.subterms[y] << std::endl;
  }
  return os;
}
