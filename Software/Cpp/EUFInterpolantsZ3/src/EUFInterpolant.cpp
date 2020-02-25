#include "EUFInterpolant.h"
#define DEBUG_EUFINTERPOLANT false

EUFInterpolant::EUFInterpolant(z3::expr const & part_a) :
  ctx(part_a.ctx()), min_id(part_a.id()), subterms(ctx),
  uncommon_positions(), uf(), horn_clauses(ctx, subterms, min_id),
  contradiction(ctx), disequalities(ctx), size(part_a.id() + 1) {
  
  contradiction = ctx.bool_val(false);
  std::vector<bool> visited(size, false);
  subterms.resize(size);
  init(part_a, min_id, visited);
  
  // There is extra padding for non-apps-z3::expressions
  unsigned aux_num_terms = size - min_id;
  unsigned aux_class_ids[aux_num_terms];
  z3::expr_vector aux_subterms(ctx);
  for(unsigned i = min_id; i < size; i++)
    aux_subterms.push_back(subterms[i]);

  z3::solver euf_solver(ctx, "QF_UF");
  euf_solver.add(part_a);
  if(euf_solver.implied_equalities(aux_num_terms, aux_subterms, aux_class_ids) != z3::unsat){
    unsigned class_ids[size];
    for(unsigned i = 0; i < size; i++){
      if(i < min_id)
	class_ids[i] = i;
      else
	class_ids[i] = aux_class_ids[i - min_id] + min_id;
    }
    uf = UnionFind(class_ids, size);
    
    disequalitiesToHCS();
    exposeUncommons();

    // Stress test -------------------------------------------------------------
    z3::sort test_sort = ctx.uninterpreted_sort("A");
    z3::expr test_y2 = ctx.constant("c_y2", test_sort);
    z3::expr test_y1 = ctx.constant("c_y1", test_sort);
    z3::expr test_s1 = ctx.constant("c_s1", test_sort);
    z3::expr test_z2 = ctx.constant("c_z2", test_sort);
    z3::expr test_v = ctx.constant("a_v", test_sort);
    z3::func_decl f = ctx.function("c_f", test_sort, test_sort, test_sort);
    
    z3::expr_vector test_body(ctx);
    test_body.push_back((test_s1 == f(test_y2, test_v)));
    z3::expr test_head = (test_y1 == f(test_y1, test_v));
    horn_clauses.add(new HornClause(uf, ctx, subterms, test_body, test_head));

    z3::expr_vector test_body2(ctx);
    test_body2.push_back((test_s1 == f(test_y2, test_v)));
    test_body2.push_back((test_y1 == f(test_y1, test_v)));
    z3::expr test_head2 = (test_y2 == test_v);
    horn_clauses.add(new HornClause(uf, ctx, subterms, test_body2, test_head2));
    // Stress test -------------------------------------------------------------
    
    UnionFind aux_uf(uf);
    Hornsat hsat(horn_clauses, aux_uf);
    auto replacements = hsat.satisfiable(aux_uf);
    
    for(auto x : replacements)
      std::cout << "Merge " << *horn_clauses[x.clause1]
		<< " with " << *horn_clauses[x.clause2] << std::endl;

    // std::cout << hsat << std::endl;

    // Keep working here
    buildInterpolant(replacements);
    
    return;
  }
  throw "Problem @ EUFInterpolant::EUFInterpolant. The z3::expr const & part_a was unsatisfiable.";
}


EUFInterpolant::~EUFInterpolant(){
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
    switch(f.decl_kind()){
    case Z3_OP_DISTINCT:
      disequalities.push_back(e);
      return;
    case Z3_OP_UNINTERPRETED:
      if(num > 0 && !e.is_common())
	uncommon_positions[f.name().str()].push_back(e.id());
    default:
      return;
    }
  }
  throw "Problem @ EUFInterpolant::init. The expression e is not an application term.";
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
    horn_clauses.add(new HornClause(uf, ctx, subterms, hc_body, contradiction));
  }
}

void EUFInterpolant::exposeUncommons(){
  for(auto iterator : uncommon_positions){
    unsigned current_num_uncomms = iterator.second.size();
    if(current_num_uncomms < 2)
      break;
    for(unsigned index_1 = 0; index_1 < current_num_uncomms - 1; index_1++)
      for(unsigned index_2 = index_1 + 1; index_2 < current_num_uncomms; index_2++){
	z3::expr t1 = subterms[iterator.second[index_1]], t2 = subterms[iterator.second[index_2]];
	z3::expr_vector hc_body = buildHCBody(t1, t2);
	z3::expr        hc_head = repr(t1) == repr(t2);
	horn_clauses.add(new HornClause(uf, ctx, subterms, hc_body, hc_head));
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
  unsigned num = euf.size;
  std::cout << "All the subterms:" << std::endl;
  for(unsigned i = euf.min_id; i < num; i++){
    std::cout << "Original: " << euf.subterms[i]
	      << " Representative " << euf.subterms[euf.uf.find(euf.subterms[i].id())] << std::endl;
  }

  std::cout << "Horn clauses produced:" << std::endl;
  for(HornClause * x : euf.horn_clauses.getHornClauses())
    std::cout << *x << std::endl;
  
  return os;
}
