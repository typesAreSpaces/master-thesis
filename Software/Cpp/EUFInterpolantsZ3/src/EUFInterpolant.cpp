#include "EUFInterpolant.h"
#define DEBUG_DESTRUCTOR_EUF false
#define DEBUG_EUFINTERPOLANT false
#define DEBUG_CURRYFICATION false

EUFInterpolant::EUFInterpolant(z3::expr const & part_a) :
  ctx(part_a.ctx()), min_id(part_a.id()), subterms(ctx),
  fsym_positions(), uf(part_a.id() + 1), horn_clauses(ctx, min_id, subterms),
  contradiction(ctx), disequalities(ctx), original_num_terms(part_a.id() + 1){
  
  contradiction = ctx.bool_val(false);
  std::vector<bool> visited(original_num_terms, false);
  subterms.resize(original_num_terms);
  pred_list.resize(original_num_terms);
  curry_nodes.resize(original_num_terms);

  // The following defines min_id, visited,
  // subterms, disequalities, fsym_positions,
  // and curry_decl
  init(part_a, min_id, visited);
  
  // --------------------------------------------------
  // The following defines curry_nodes
  for(unsigned i = min_id; i < original_num_terms; i++)
    curry_nodes[i] = new CurryNode(i);
  std::fill(visited.begin(), visited.end(), false);
  curryfication(part_a, visited);

  for(unsigned i = min_id; i < original_num_terms; i++)
    std::cout << *curry_nodes[i] << std::endl;
  
  // --------------------------------------------------
  
  // -------------------------------------------------------------------------
  // //                       ---------
  // // The following defines |pred_list|. 
  // //                       ---------  
  // initCCList(part_a);
  // // The following sets up a
  // // --------------------
  // // |congruence closure| data structure.
  // // --------------------
  // //                   ----
  // // After this point, |uf| is fully defined
  // //                   ----
  // CongruenceClosureNO cc(min_id, subterms, pred_list, uf);
  // processEqs(part_a, cc);
  // -------------------------------------------------------------------------
  //                       ---------                    ----
  // The following defines |pred_list|. After this point, |uf| is fully defined.
  //                       ---------                    ----
  processEqs(part_a);

  // ----------------------------------------------------
  // The following sets up a
  // --------------------
  // |congruence closure| data structure
  // --------------------
  CongruenceClosureDST cc(min_id, subterms, pred_list, uf);
  std::list<unsigned> pending;
  
  for(unsigned i = min_id; i < original_num_terms; i++)
    if(subterms[i].num_args() > 0)
      pending.push_back(i);
  cc.buildCongruenceClosure(pending);
  assert(pending.empty());
  // ----------------------------------------------------

  // KEEP: working here
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
  // CCList hornsat_list(pred_list);
  // assert(pred_list.size() == subterms.size());
  // UnionFind hornsat_uf(uf);
  // hornsat_uf.increaseSize(subterms.size());
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
  // throw "Problem @ EUFInterpolant::EUFInterpolant. The z3::expr const & part_a was unsatisfiable.";
}
  
EUFInterpolant::~EUFInterpolant(){  
  for(auto x : extra_nodes)
    delete x;

  for(auto x : curry_decl)
    delete x.second;
  curry_decl.clear();

#if DEBUG_DESTRUCTOR_EUF
  std::cout << "Bye EUFInterpolant" << std::endl;
#endif
}

void EUFInterpolant::init(z3::expr const & e, unsigned & min_id, std::vector<bool> & visited){
  if(e.is_app()){
    if(e.id() < min_id)
      min_id = e.id();
    if(visited[e.id()])
      return;
    
    visited[e.id()] = true;
    subterms.set(e.id(), (z3::expr&) e);
    
    unsigned num = e.num_args();
    for(unsigned i = 0; i < num; i++)
      init(e.arg(i), min_id, visited);
    
    z3::func_decl f = e.decl();
    if(curry_decl[f.id()] == nullptr)
      curry_decl[f.id()] = new CurryNode(e.id(), f.name().str(), nullptr, nullptr);
    
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

void EUFInterpolant::curryfication(z3::expr const & e,
				   std::vector<bool> & visited){

#if DEBUG_CURRYFICATION
  std::cout << "curryfing this " << e << " " << e.id() << std::endl;
#endif
  
  if(e.is_app()){

    if(visited[e.id()])
      return;
    visited[e.id()] = true;
    
    unsigned num = e.num_args();
    
    for(unsigned i = 0; i < num; i++)
      curryfication(e.arg(i), visited);
    
    // Update curry_nodes
    
    if(num > 0){
      unsigned last_node_pos = extra_nodes.size(),
    	new_last_node_pos = last_node_pos + num;
      extra_nodes.resize(new_last_node_pos);
      
      for(unsigned i = last_node_pos; i < new_last_node_pos; i++)
    	extra_nodes[i] = new CurryNode(i, "apply", nullptr, nullptr);
      
      // Case for first argument
      extra_nodes[last_node_pos]->update("apply",
					 curry_decl[e.decl().id()],
					 curry_nodes[e.arg(0).id()]);
      // Case for the rest of the arguments
      for(unsigned i = 1; i < num; i++)
      	extra_nodes[last_node_pos + i]->update("apply",
					       extra_nodes[last_node_pos + i - 1],
					       curry_nodes[e.arg(i).id()]);

      extra_nodes[new_last_node_pos - 1]->changeId(curry_nodes[e.id()]->getId());
#if DEBUG_CURRYFICATION
      std::cout << "Before (func term) " << *(curry_nodes[e.id()]) << " "
		<< (curry_nodes[e.id()] == extra_nodes[new_last_node_pos - 1]) << std::endl;
#endif

      delete curry_nodes[e.id()];
      curry_nodes[e.id()] = extra_nodes[new_last_node_pos - 1];
      
#if DEBUG_CURRYFICATION
      std::cout << "After (func term) " << *(curry_nodes[e.id()]) << std::endl;
#endif
    }
    else{
#if DEBUG_CURRYFICATION
      std::cout << "Before (constant) " << *(curry_nodes[e.id()]) << " "
		<< (curry_nodes[e.id()] == curry_decl[e.decl().id()]) << std::endl;
#endif      
      delete curry_nodes[e.id()];
      curry_nodes[e.id()] = curry_decl[e.decl().id()];

#if DEBUG_CURRYFICATION
      std::cout << "After (constant) " << *(curry_nodes[e.id()]) << std::endl;
#endif
    }

    return;
  }
  
  throw "Problem @ EUFInterpolant::curryfication(z3::expr const &). The z3::expr const & is not an app.";
}

// Actually, this function is used to setup up the pred_list
// for the Nelson-Oppen Congruence Closure
void EUFInterpolant::initCCList(z3::expr const & e){
  if(e.is_app()){
    unsigned num = e.num_args();
    for(unsigned i = 0; i < num; i++){
      // The following function is used to
      // keep the invariant that elements in pred_list
      // are unique and sorted
      insert(pred_list[e.arg(i).id()], e.id());
      initCCList(e.arg(i));
    }
    return;
  }
  throw "Problem @ EUFInterpolant::initCCList. The expression e is not an application term.";
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
    horn_clauses.add(new HornClause(uf, ctx, min_id, subterms, hc_body, contradiction, pred_list));
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
	    horn_clauses.add(new HornClause(uf, ctx, min_id, subterms, hc_body, hc_head, pred_list));
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
  unsigned num = euf.original_num_terms, num_changes = 0;
  std::cout << "All the original subterms:" << std::endl;
  for(unsigned i = euf.min_id; i < num; i++){
    // std::cout << "Original: " << i
    // 	      << " Representative " << euf.uf.find(i) << std::endl;
    
    std::cout << i << ". "
	      << ((i == euf.uf.find(i)) ? "(Same)" : "(Different)")
	      << " Original: " << euf.subterms[i]
	      << " Representative " << euf.subterms[euf.uf.find(euf.subterms[i].id())] << std::endl;
    if(i != euf.uf.find(i))
      num_changes++;
  }

  std::cout << "Horn clauses produced:" << std::endl;
  for(HornClause * x : euf.horn_clauses.getHornClauses())
    std::cout << *x << std::endl;
  std::cout << "Number of differences between term and its representative: " << num_changes;
  return os;
}
