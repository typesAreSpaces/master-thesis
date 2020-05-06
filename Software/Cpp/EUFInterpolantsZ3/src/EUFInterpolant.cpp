#include "EUFInterpolant.h"
#define DEBUG_DESTRUCTOR_EUF 0
#define DEBUG_EUFINTERPOLANT 0
#define DEBUG_CURRYFICATION  0
#define DEBUG_SUBTERMS       1
#define DEBUG_INIT           1

EUFInterpolant::EUFInterpolant(z3::expr const & input_formula) :
  original_num_terms(input_formula.id() + 1),
  ctx(input_formula.ctx()), subterms(ctx), contradiction(ctx.bool_val(false)), disequalities(ctx),
  fsym_positions(), uf(input_formula.id() + 1), pred_list(), horn_clauses(ctx, subterms),
  curry_decl(), factory_curry_nodes(original_num_terms, curry_decl)
{        

  subterms .resize(original_num_terms);
  pred_list.resize(original_num_terms);

  // The following defines: 
  // subterms, disequalities, fsym_positions,
  // and curry_decl
  init(input_formula);

  // FIX: There is a gap between the actual min_id.
#if 0 
  for(auto it = subterms.begin(); it != subterms.end(); ++it){
    std::cout << *it << std::endl;
  }      
#endif 

  CongruenceClosureExplain cc(subterms, pred_list, uf, factory_curry_nodes);

  std::cout << "Print factory_curry_nodes" << std::endl;
  std::cout << factory_curry_nodes << std::endl;

  // Testing
  //cc.giveExplanation(std::cout, subterms[5], subterms[11]);
  //cc.giveExplanation(std::cout, subterms[5], subterms[6]);
  //cc.giveExplanation(std::cout, subterms[6], subterms[5]);

#if 0
  auto explanation = cc.explain(subterms[6], subterms[5]);
  if(explanation.size() != 0){
    unsigned num = 1;
    for(auto label : explanation){
      assert(label->tag == EQ);
      std::cout << "Prototype Label " << num++ << ":" << std::endl;
      std::cout << subterms[label->eq_cn.lhs.getZ3Id()] << std::endl;
      std::cout << subterms[label->eq_cn.rhs.getZ3Id()] << std::endl;
    }
  }
#endif

  // // Converting disequalities to Horn Clauses
  // disequalitiesToHCS();

  // // Unconditional uncommon symbol elimination step
  // //                   --------------
  // // After this point, |horn_clauses| is fully defined
  // //                   --------------
  // exposeUncommons();
  // // std::cout << horn_clauses << std::endl;

  // // // ----------------------------------------------------------------------
  // // Additional data structures for conditional uncommon symbol elimination
  // PredList hornsat_list(pred_list);
  // assert(pred_list.size() == subterms.size());

  // UnionFind hornsat_uf(uf);
  // hornsat_uf.resize(subterms.size());
  // CongruenceClosureDST hornsat_cc(min_id, subterms, hornsat_list, hornsat_uf);
  // Hornsat hsat(horn_clauses, hornsat_uf);
  // // // ----------------------------------------------------------------------

  // auto replacements = hsat.satisfiable(hornsat_cc);
  // for(auto x : replacements)
  //   std::cout << "Merge " << *horn_clauses[x.clause1]
  // 	      << " with " << *horn_clauses[x.clause2] << std::endl;

  // // // ----------------------------
  // // std::cout << hsat << std::endl;
  // // // ----------------------------

  // buildInterpolant(replacements);

  return;
  // throw "Problem @ EUFInterpolant::EUFInterpolant. The z3::expr const & input_formula was unsatisfiable.";
}

EUFInterpolant::~EUFInterpolant(){
#if DEBUG_DESTRUCTOR_EUF
  std::cout << "Bye EUFInterpolant" << std::endl;
#endif
}

void EUFInterpolant::init(z3::expr const & e){
  if(e.is_app()){
    if(subterms.visited[e.id()])
      return;

    subterms.visited[e.id()] = true;
    subterms.set(e.id(), e);

    unsigned num = e.num_args();
    for(unsigned i = 0; i < num; i++)
      init(e.arg(i));

    z3::func_decl f = e.decl();
    if(curry_decl[f.id()] == nullptr)
      curry_decl[f.id()] = factory_curry_nodes.newCurryNode(e.id(), f.name().str(), nullptr, nullptr);

    switch(f.decl_kind()){
      case Z3_OP_DISTINCT:
        disequalities.push_back(e);
        return;
      case Z3_OP_UNINTERPRETED:
        if(num > 0)
          fsym_positions[f.name().str()].push_back(e.id());
      default:
        return;
    }
  }
  throw "Problem @ EUFInterpolant::init. The expression e is not an application term.";
}

// Actually, this function is used to setup up the pred_list
// for the Nelson-Oppen Congruence Closure
void EUFInterpolant::initPredList(z3::expr const & e){
  if(e.is_app()){
    unsigned num = e.num_args();
    for(unsigned i = 0; i < num; i++){
      // The following function is used to
      // keep the invariant that elements in pred_list
      // are unique and sorted
      insert(pred_list[e.arg(i).id()], e.id());
      initPredList(e.arg(i));
    }
    return;
  }
  throw "Problem @ EUFInterpolant::initPredList. The expression e is not an application term.";
}

void EUFInterpolant::processEqs(z3::expr const & e){
  if(e.is_app()){ 
    unsigned num = e.num_args();
    for(unsigned i = 0; i < num; i++){
      pred_list[e.arg(i).id()].push_back(e.id());
      processEqs(e.arg(i));
    }

    z3::func_decl f = e.decl();
    switch(f.decl_kind()){
      case Z3_OP_EQ:
        if(HornClause::compareTerm(e.arg(0), e.arg(1)))
          uf.combine(e.arg(1).id(), e.arg(0).id());
        else
          uf.combine(e.arg(0).id(), e.arg(1).id());
        return;
      default:
        return;
    }
  }
  throw "Problem @ EUFInterpolant::processEqs(z3::expr const &). The expression e is not an application term.";
}

void EUFInterpolant::processEqs(z3::expr const & e, CongruenceClosureNO & cc_no){
  if(e.is_app()){ 
    unsigned num = e.num_args();
    for(unsigned i = 0; i < num; i++)
      processEqs(e.arg(i), cc_no);

    z3::func_decl f = e.decl();
    switch(f.decl_kind()){
      case Z3_OP_EQ:
        if(HornClause::compareTerm(e.arg(0), e.arg(1)))
          cc_no.combine(e.arg(1).id(), e.arg(0).id());
        else
          cc_no.combine(e.arg(0).id(), e.arg(1).id());
        return;
      default:
        return;
    }
  }
  throw "Problem @ EUFInterpolant::processEqs(z3::expr const &, CongruenceClosureNO &). The expression e is not an application term.";
}

z3::expr EUFInterpolant::repr(const z3::expr & t){
  return subterms[uf.find(t.id())];
}

z3::expr_vector EUFInterpolant::buildHCBody(z3::expr const & t1, z3::expr const & t2){
  z3::expr_vector hc_body(ctx);
  unsigned num_args = t1.num_args();
  for(unsigned i = 0; i < num_args; i++)
    hc_body.push_back(repr(t1.arg(i)) == repr(t2.arg(i)));
  return hc_body;
}

void EUFInterpolant::disequalitiesToHCS(){
  unsigned num_disequalities = disequalities.size();
  for(unsigned i = 0; i < num_disequalities; i++){
    z3::expr_vector hc_body(ctx);
    hc_body.push_back(repr(disequalities[i].arg(0)) == repr(disequalities[i].arg(1)));
    horn_clauses.add(new HornClause(uf, ctx, subterms, hc_body, contradiction, pred_list));
  }
}

void EUFInterpolant::exposeUncommons(){
  for(auto iterator : fsym_positions){
    unsigned current_num = iterator.second.size();
    if(current_num >= 2)
      for(unsigned index_1 = 0; index_1 < current_num - 1; index_1++)
        for(unsigned index_2 = index_1 + 1; index_2 < current_num; index_2++){
          z3::expr t1 = subterms[iterator.second[index_1]], t2 = subterms[iterator.second[index_2]];
          // Only expose terms if at least one term is uncommon
          if(!t1.is_common() || !t2.is_common()){
            z3::expr_vector hc_body = buildHCBody(t1, t2);
            z3::expr        hc_head = repr(t1) == repr(t2);
            horn_clauses.add(new HornClause(uf, ctx, subterms, hc_body, hc_head, pred_list));
          }
        }
  }
  return;
}

z3::expr_vector EUFInterpolant::conditionalReplacement(z3::expr_vector & terms_to_replace){ // TODO:
  return terms_to_replace;
}


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

z3::expr EUFInterpolant::buildInterpolant(std::vector<Replacement> replacements){
  horn_clauses.conditionalElimination(replacements); // TODO: Implement the following

  // auto non_reducible_hs_z3 = cvt.convert(horn_clauses.getHornClauses());
  // auto simplified_hs = cvt.extraSimplification(non_reducible_hs_z3);  
  // auto reducible_hs = horn_clauses.getReducibleHornClauses();
  // auto reducible_hs_z3 = cvt.convert(reducible_hs);
  // auto equations = cvt.convert(original_closure.getEquations());

  z3::expr_vector terms_to_replace(ctx);
  // horn_clauses.getTermsToReplace(terms_to_replace); // TODO: Implement the following

  auto interpolant = conditionalReplacement(terms_to_replace);

  // auto simplified_exponential_hs = cvt.extraSimplification(exponential_hs);

  // return cvt.makeConjunction(simplified_hs) && cvt.makeConjunction(simplified_exponential_hs);
  return z3::mk_and(interpolant);
}

std::ostream & operator << (std::ostream & os, EUFInterpolant & euf){
  return os;
}
