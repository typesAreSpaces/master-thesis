#include "ThCombInterpolator.h"

bool ThCombInterpolator::z3_const_comparator::operator() (
    z3::expr const & e1, z3::expr const & e2){
  return e1.id() < e2.id();
}

ThCombInterpolator::ThCombInterpolator(
    z3::expr_vector const & formula_a, z3::expr_vector const & formula_b) :
  ctx(formula_a.ctx()), 
  part_a(formula_a), part_b(formula_b),
  euf_solver(ctx, "QF_UF"), oct_solver(ctx, "QF_LIA"),
  shared_variables(ctx), partial_interpolants(ctx)
{
  sharedVariables(part_a, part_b);
#if _DEBUG_TH_COMB_
  std::cout << "Part a" << std::endl;
  std::cout << part_a;
  std::cout << "Part b" << std::endl;
  std::cout << part_b;
  std::cout << "Shared variables" << std::endl;
  std::cout << shared_variables << std::endl;
#endif

  for(auto const & form : part_a.getOctComponent())
    oct_solver.add(form);
  for(auto const & form : part_b.getOctComponent())
    oct_solver.add(form);
  for(auto const & form : part_a.getEufComponent())
    euf_solver.add(form);
  for(auto const & form : part_b.getEufComponent())
    euf_solver.add(form);

  // Find theory that unsat by passing 
  // disjuntions of shared equalities
  DisjEqsPropagator phi(shared_variables);
  auto current_disj_eqs = phi.begin();

  // Commet: Z3 simplies formulas while checking
  // for consistency

  while(!current_disj_eqs.isLast()){
#if _DEBUG_TH_COMB_
    std::cout << "(inside main loop) current disj eqs" << std::endl;
    std::cout << *current_disj_eqs << std::endl;
#endif
    oct_solver.push();
    if(oct_solver.check() == z3::unsat){
      std::cout << "OCT solver found a contradiction" << std::endl;
      std::cout << oct_solver.assertions() << std::endl;
      // TODO:
      //std::cout << "assertions in OCT" << std::endl;
      //for(auto const & x : oct_solver.assertions())
      //std::cout << x << std::endl;
      //auto const & oct_assertions = oct_solver.assertions();
      //CDCL_T cdcl_t(oct_assertions);
      //cdcl_t.toDimacsFile();
      //ProofFactory resolution_proof = ProofFactory();
      return;
    }
    oct_solver.pop();
    euf_solver.push();
    if(euf_solver.check() == z3::unsat){
      std::cout << "EUF solver found a contradiction" << std::endl;
      std::cout << euf_solver.assertions() << std::endl;
      // TODO:
      //std::cout << "assertions in EUF" << std::endl;
      //for(auto const & x : euf_solver.assertions())
      //std::cout << x << std::endl;
      //auto const & euf_assertions = euf_solver.assertions();
      //CDCL_T cdcl_t(euf_assertions);
      //cdcl_t.toDimacsFile();
      //ProofFactory resolution_proof = ProofFactory();
      return;
    }
    euf_solver.pop();

    euf_solver.push();
    euf_solver.add(not(*current_disj_eqs));
    if(euf_solver.check() == z3::unsat){
      oct_solver.push();
      oct_solver.add(not(*current_disj_eqs));
      if(oct_solver.check() == z3::unsat){
        euf_solver.pop();
        oct_solver.pop();
        ++current_disj_eqs;
        continue;
      }
      euf_solver.pop();
      oct_solver.pop();
      oct_solver.add(*current_disj_eqs);
      // TODO:
      current_disj_eqs = phi.begin();
      continue;
    }

    oct_solver.push();
    oct_solver.add(not(*current_disj_eqs));
    if(oct_solver.check() == z3::unsat){
      euf_solver.pop();
      oct_solver.pop();
      euf_solver.add(*current_disj_eqs);
      // TODO:
      current_disj_eqs = phi.begin();
      continue;
    }
    euf_solver.pop();
    oct_solver.pop();
    ++current_disj_eqs;
  } 

  // TODO:
  //
  // Build partial interpolants for:
  // - Rename the proof tree in term of the non-propositonal
  // elements
  // - Convex case
  // - Partial interpolant for conflict clauses
  
  std::cout << "The input-formula is satisfiable" << std::endl;
  return;
}

ThCombInterpolator::~ThCombInterpolator(){
}

void ThCombInterpolator::sharedVariables(Purifier const & part_a, Purifier const & part_b){
  z3_expr_set oct_set({});
  z3_expr_set euf_set({});

  for(auto const & formula : part_a.getOctComponent())
    collectVariables(formula, oct_set);
  for(auto const & formula : part_b.getOctComponent())
    collectVariables(formula, oct_set);

  for(auto const & formula : part_a.getEufComponent())
    collectVariables(formula, euf_set);
  for(auto const & formula : part_b.getEufComponent())
    collectVariables(formula, euf_set);

  for(auto const & formula : oct_set)
    if(euf_set.find(formula) != euf_set.end())
      shared_variables.push_back(formula);
}

void ThCombInterpolator::collectVariables(z3::expr const & e, z3_expr_set & _set){
  if(e.is_app()){

    auto f = e.decl().decl_kind();
    switch(f){
      case Z3_OP_UNINTERPRETED:
        {
          unsigned num_args = e.num_args();
          if(num_args == 0){
            _set.insert(e);
            return;
          }
          for(unsigned _i = 0; _i < num_args; ++_i)
            collectVariables(e.arg(_i), _set);
          return;
        }
      default: 
        {
          unsigned num_args = e.num_args();
          for(unsigned _i = 0; _i < num_args; ++_i)
            collectVariables(e.arg(_i), _set);
          return;
        }
    }
  }
  throw "Error @ Purifier::aux_update_shared_vars"
    "The expression is not an application";
}

void ThCombInterpolator::checkImpliedEqualities(z3::expr_vector & terms, z3::solver & s){

  unsigned num_terms = terms.size();
  unsigned class_ids[num_terms];

  for(unsigned i = 0; i < num_terms; i++)
    class_ids[i] = 0;

  switch(s.check_implied_equalities(num_terms, terms, class_ids)){
    case z3::sat:
      std::cout << "sat" << std::endl;
      for(unsigned i = 0; i < num_terms; i++)
        std::cout << "Class " << terms[i] 
          << " -> " << class_ids[i] << std::endl;
      return;
    case z3::unsat:
      std::cout << "unsat" << std::endl;
      return;
    case z3::unknown:
      std::cout << "unknown" << std::endl;
      return;
  }
}

z3::expr ThCombInterpolator::partialInterpolantConvex(){
  return ctx.bool_val(true);
}

z3::expr ThCombInterpolator::partialInterpolantConflictClause(){
  return ctx.bool_val(true);
}

z3::expr ThCombInterpolator::partialInterpolantUnitResolution(z3::expr const & partial_c1, z3::expr const & x){
  unsigned temp_size = x.num_args();
  z3::expr partial_x = partial_interpolants.find(x.arg(temp_size - 1));
  if(x.is_common())
    return ((x || partial_c1) && (not(x) || partial_x));
  else if(x.is_a_pure()){
    return (partial_c1 || partial_x);
  }
  else{
    return (partial_c1 && partial_x);
  }
}

void ThCombInterpolator::getInterpolant(){
}

std::ostream & operator << (std::ostream & os, ThCombInterpolator & p){
  //z3::solver aux_solver(p.ctx, "QF_UFLIA");

  //p.part_a.addEufFormulasToSolver(aux_solver);
  //p.part_a.addOctFormulasToSolver(aux_solver);
  //p.part_b.addEufFormulasToSolver(aux_solver);
  //p.part_b.addOctFormulasToSolver(aux_solver);

  //if(aux_solver.check() == z3::unsat){
    //p.traverseProof1(aux_solver.proof());
  //}

  os << "Returns interpolant";
  return os;
}
