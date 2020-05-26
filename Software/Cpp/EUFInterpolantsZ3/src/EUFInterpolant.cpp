#include "EUFInterpolant.h"

EUFInterpolant::EUFInterpolant(z3::expr_vector const & assertions) : Input(assertions)
{        
  // Unconditional uncommon symbol elimination step
  exposeUncommons();
#if DEBUG_EXPOSE_UNCOMMS
  std::cout << "After expose uncommons" << std::endl;
  std::cout << horn_clauses << std::endl;
#endif

  // Conditional uncommon symbol elimination step
  Hornsat hsat(cce, horn_clauses);
#if DEBUG_COND_ELIM
  std::cout << hsat << std::endl;
#endif

  // buildInterpolant(replacements);
  return;
}

EUFInterpolant::~EUFInterpolant(){
#if DEBUG_DESTRUCTOR_EUF
  std::cout << "Bye EUFInterpolant" << std::endl;
#endif
}

z3::expr_vector EUFInterpolant::buildHCBody(z3::expr const & t1, z3::expr const & t2){
  z3::expr_vector hc_body(ctx);
  unsigned num_args = t1.num_args();
  for(unsigned i = 0; i < num_args; i++)
    hc_body.push_back(z3_repr(t1.arg(i)) == z3_repr(t2.arg(i)));
  return hc_body;
}

void EUFInterpolant::exposeUncommons(){
  for(auto iterator : fsym_positions){
    unsigned current_num = iterator.second.size();
    if(current_num >= 2)
      for(unsigned index_1 = 0; index_1 < current_num - 1; index_1++)
        for(unsigned index_2 = index_1 + 1; index_2 < current_num; index_2++){
          z3::expr const & t1 = subterms[iterator.second[index_1]], & t2 = subterms[iterator.second[index_2]];
          // Only expose terms if at least one term is uncommon
          if(!t1.is_common() || !t2.is_common()){
            z3::expr_vector hc_body = buildHCBody(t1, t2);
            z3::expr        hc_head = z3_repr(t1) == z3_repr(t2);
            horn_clauses.add(new HornClause(ctx, hc_body, hc_head, ufe));
          }
        }
  }
  return;
}

z3::expr EUFInterpolant::buildInterpolant(std::vector<Replacement> replacements){
  throw "Not implemented yet!";
  //horn_clauses.conditionalElimination(replacements); 

  // auto non_reducible_hs_z3 = cvt.convert(horn_clauses.getHornClauses());
  // auto simplified_hs = cvt.extraSimplification(non_reducible_hs_z3);  
  // auto reducible_hs = horn_clauses.getReducibleHornClauses();
  // auto reducible_hs_z3 = cvt.convert(reducible_hs);
  // auto equations = cvt.convert(original_closure.getEquations());

  //z3::expr_vector terms_to_replace(ctx);
  // horn_clauses.getTermsToReplace(terms_to_replace);

  //auto interpolant = conditionalReplacement(terms_to_replace);

  // auto simplified_exponential_hs = cvt.extraSimplification(exponential_hs);

  // return cvt.makeConjunction(simplified_hs) && cvt.makeConjunction(simplified_exponential_hs);
  //return z3::mk_and(interpolant);
}

std::ostream & operator << (std::ostream & os, EUFInterpolant & euf){
  return os;
}
