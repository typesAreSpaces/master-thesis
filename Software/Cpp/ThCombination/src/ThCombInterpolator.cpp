#include "ThCombInterpolator.h"
#include <z3++.h>

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

  for(auto const & form : part_a.getOctComponent()){
    oct_solver.add(form);
    partial_interpolants.insert(form, ctx.bool_val(false));
  }
  for(auto const & form : part_b.getOctComponent()){
    oct_solver.add(form);
    partial_interpolants.insert(form, ctx.bool_val(true));
  }
  for(auto const & form : part_a.getEufComponent()){
    euf_solver.add(form);
    partial_interpolants.insert(form, ctx.bool_val(false));

  }
  for(auto const & form : part_b.getEufComponent()){
    euf_solver.add(form);
    partial_interpolants.insert(form, ctx.bool_val(true));
  }

  // Find theory that unsat by passing 
  // disjuntions of shared equalities
  DisjEqsPropagator phi(shared_variables);
  auto current_disj_eqs = phi.begin();


  while(!current_disj_eqs.isLast()){
    auto current_disj_eqs_form = *current_disj_eqs;
    oct_solver.push();
    if(oct_solver.check() == z3::unsat){
      std::cout << "OCT solver found a contradiction" << std::endl;
      std::cout << oct_solver.assertions() << std::endl;
      // ----------------------------------------------------
      // TODO: compute final interpolant
      PicoProofFactory resolution_proof = PicoProofFactory();
      //std::cout << resolution_proof << std::endl;

      // TODO: keep working here!
      // ----------------------------------------------------
      return;
    }
    oct_solver.pop();
    euf_solver.push();
    if(euf_solver.check() == z3::unsat){
      std::cout << "EUF solver found a contradiction" << std::endl;
      std::cout << euf_solver.assertions() << std::endl;
      // ----------------------------------------------------
      // TODO: compute final interpolant
      PicoProofFactory resolution_proof = PicoProofFactory();
      //std::cout << resolution_proof << std::endl;

      // TODO: keep working here!
      // ----------------------------------------------------
      return;
    }
    euf_solver.pop();

    euf_solver.push();
    euf_solver.add(not(current_disj_eqs_form));
    if(euf_solver.check() == z3::unsat){
      oct_solver.push();
      oct_solver.add(not(current_disj_eqs_form));
      if(oct_solver.check() == z3::unsat){
        euf_solver.pop();
        oct_solver.pop();
        ++current_disj_eqs;
        continue;
      }
      euf_solver.pop();
      oct_solver.pop();
      // ---------------------------------------------------
      // TODO: compute partial interpolants!
      std::cout << "Disjunction implied in EUF: "
        << current_disj_eqs_form
        << std::endl;
      
      z3::expr_vector euf_assertions(ctx);
      for(auto const & assertion : euf_solver.assertions())
        euf_assertions.push_back(assertion);
      if(current_disj_eqs_form.decl().decl_kind() == Z3_OP_OR){
        unsigned num_arg_disj = current_disj_eqs_form.num_args();
        for(unsigned _i = 0; _i < num_arg_disj; ++_i)
          euf_assertions.push_back(
              not(current_disj_eqs_form.arg(_i)));
      }
      else{
        assert(current_disj_eqs_form.decl().decl_kind() == Z3_OP_EQ);
        euf_assertions.push_back(not(current_disj_eqs_form));
      }
      //euf_assertions.push_back(not(current_disj_eqs_form));

      CDCL_T cdcl_euf(euf_assertions);
      cdcl_euf.toDimacsFile();
      
      PicoProofFactory resolution_proof = PicoProofFactory();
      partialInterpolantNonConvex(cdcl_euf, resolution_proof, current_disj_eqs_form);

      // TODO: keep working here!
      // ---------------------------------------------------
      oct_solver.add(current_disj_eqs_form);
      current_disj_eqs = phi.begin();
      continue;
    }

    oct_solver.push();
    oct_solver.add(not(current_disj_eqs_form));
    if(oct_solver.check() == z3::unsat){
      euf_solver.pop();
      oct_solver.pop();
      // ---------------------------------------------------
      // TODO: compute partial interpolants!
      std::cout << "Disjunction implied in OCT: "
        << current_disj_eqs_form
        << std::endl;

      z3::expr_vector oct_assertions(ctx);
      for(auto const & assertion : oct_solver.assertions())
        oct_assertions.push_back(assertion);
      if(current_disj_eqs_form.decl().decl_kind() == Z3_OP_OR){
        unsigned num_arg_disj = current_disj_eqs_form.num_args();
        for(unsigned _i = 0; _i < num_arg_disj; ++_i)
          oct_assertions.push_back(
              not(current_disj_eqs_form.arg(_i)));
      }
      else{
        assert(current_disj_eqs_form.decl().decl_kind() == Z3_OP_EQ);
        oct_assertions.push_back(not(current_disj_eqs_form));
      }
      //oct_assertions.push_back(not(current_disj_eqs_form));

      CDCL_T cdcl_oct(oct_assertions);
      cdcl_oct.toDimacsFile();

      PicoProofFactory resolution_proof = PicoProofFactory();
      partialInterpolantNonConvex(cdcl_oct, resolution_proof, current_disj_eqs_form);

      // TODO: keep working here!
      // ---------------------------------------------------

      euf_solver.add(current_disj_eqs_form);
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

void ThCombInterpolator::partialInterpolantConvex(){
  //return ctx.bool_val(true);
}

void ThCombInterpolator::partialInterpolantConflictClause(){
  //return ctx.bool_val(true);
}

void ThCombInterpolator::partialInterpolantUnitResolution(z3::expr const & partial_c1, z3::expr const & x){
  unsigned temp_size = x.num_args();
  z3::expr partial_x = partial_interpolants.find(x.arg(temp_size - 1));
  //if(x.is_common())
    //return ((x || partial_c1) && (not(x) || partial_x));
  //else if(x.is_a_pure()){
    //return (partial_c1 || partial_x);
  //}
  //else{
    //return (partial_c1 && partial_x);
  //}
}

void ThCombInterpolator::partialInterpolantNonConvex(CDCL_T & cdcl_t, 
    PicoProofFactory const & pf, z3::expr const & formula){

  unsigned id        = 0;
  z3::expr predicate = ctx.bool_val(true);

  for(auto const & res_proof : pf.getProofTable()){
    bool is_fact = res_proof.subproof_1 == -1 && res_proof.subproof_2 == -1;

    // Skip element in proof table if it is not defined
    if(res_proof.size() == 0 && is_fact) {
      id++;
      continue; 
    }

    std::cout << "Clause Id: " << id++;

    if(is_fact){
      std::cout << " (Fact|";
      if(res_proof.size() == 1){
        std::cout << "Literal): ";
        if(res_proof[0] < 0)
          predicate = not(cdcl_t.concretizeAbstraction(-res_proof[0]));
        else
          predicate = cdcl_t.concretizeAbstraction(res_proof[0]);

        std::cout << "(" << predicate;

        if(partial_interpolants.contains(predicate))
          std::cout << ", interp: " << partial_interpolants.find(predicate);
        else{
          // TODO;
          // This is a conflict clause that hasn't been processed!
          // Compute conflict clause interpolant
          std::cout << ", interp: _";
        }
        std::cout << ")" << std::endl;

        continue;
      }

      assert(res_proof.size() > 1);
      z3::expr_vector conflict_clauses(ctx);
      std::cout << "Conflict Clause): ";
      for(auto const & literal : res_proof){
        if(literal < 0)
          conflict_clauses.push_back(not(cdcl_t.concretizeAbstraction(-literal)));
        else
          conflict_clauses.push_back(cdcl_t.concretizeAbstraction(literal));
      }
      // TODO;
      // Compute conflict clause interpolant
      std::cout << z3::mk_or(conflict_clauses) << std::endl;
      continue;
    }

    std::cout << " (Derived(" + std::to_string(res_proof.subproof_1) 
      + "," + std::to_string(res_proof.subproof_2) + "))";
    z3::expr_vector conflict_clauses(ctx);
    std::cout << " Clause: ";
    for(auto const & literal : res_proof){
      if(literal < 0)
        conflict_clauses.push_back(not(cdcl_t.concretizeAbstraction(-literal)));
      else
        conflict_clauses.push_back(cdcl_t.concretizeAbstraction(literal));
    }
    // TODO;
    // Compute resolution interpolant
    std::cout << z3::mk_or(conflict_clauses) << " ";
    assert(res_proof.pivot > 0);
    predicate = cdcl_t.concretizeAbstraction(res_proof.pivot);
    std::cout << " Pivot: " << predicate << std::endl;
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
