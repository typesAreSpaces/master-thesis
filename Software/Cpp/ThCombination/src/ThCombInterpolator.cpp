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
  shared_variables(ctx), partial_interpolants(ctx),
  computed_interpolant(ctx)
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

  z3::expr last_formula_added = ctx.bool_val(false);
  z3::solver
    euf_solver(ctx, "QF_UF"), oct_solver(ctx, "QF_LIA");

  for(auto const & form : part_a.getOctComponent()){
    oct_solver.add(form);
    partial_interpolants.insert(form, ctx.bool_val(false));
    DEBUG_LOOP_MSG(form << std::endl);
  }
  for(auto const & form : part_b.getOctComponent()){
    oct_solver.add(form);
    partial_interpolants.insert(form, ctx.bool_val(true));
    DEBUG_LOOP_MSG(form << std::endl);
  }
  for(auto const & form : part_a.getEufComponent()){
    euf_solver.add(form);
    partial_interpolants.insert(form, ctx.bool_val(false));
    DEBUG_LOOP_MSG(form << std::endl);
  }
  for(auto const & form : part_b.getEufComponent()){
    euf_solver.add(form);
    partial_interpolants.insert(form, ctx.bool_val(true));
    DEBUG_LOOP_MSG(form << std::endl);
  }

  // Find theory that unsat by passing 
  // disjuntions of shared equalities
  DisjEqsPropagator phi(shared_variables);
  auto current_disj_eqs = phi.begin();

  while(!current_disj_eqs.isLast()){
    // ----------------------------------------------------------------
    // Check if any solver unsats
    oct_solver.push();
    if(oct_solver.check() == z3::unsat){
      DEBUG_LOOP_MSG("OCT solver found a contradiction" << std::endl);
      DEBUG_LOOP_MSG(oct_solver.assertions() << std::endl);

      z3::expr_vector oct_assertions(ctx);
      for(auto const & assertion : oct_solver.assertions())
        oct_assertions.push_back(assertion);
      CDCL_T cdcl_oct(oct_assertions, OCT);
      cdcl_oct.toDimacsFile();
      PicoProofFactory resolution_proof = PicoProofFactory();
      partialInterpolantNonConvex(
          cdcl_oct,
          resolution_proof,
          ctx.bool_val(false),
          oct_assertions.size(), EUF);
      z3::expr_vector existential_quants(ctx);
      for(unsigned _i = 0; _i < phi.ab_mixed_index; ++_i)
        existential_quants.push_back(ctx.int_const(("c_t_" + std::to_string(_i)).c_str()));
      computed_interpolant = z3::exists(existential_quants,
          partial_interpolants.find(ctx.bool_val(false))).simplify();
      DEBUG_LOOP_MSG(
          "-> Final Interpolant: " 
          << computed_interpolant
          << std::endl);
      // This should be allowed 
      // when lift procedures are 
      // given for all the 
      // theories involved
#if 0 
      // *+*+*+*+*+*+*+*+*+*+*+*+*+*+*+*+*+*+*+*+*+*+*+*+*+*+*+*+
      // TODO: get all the witness terms introduced
      // and obtain their representatives (these should be common)
      // Eliminate the witness terms using the solve-eqs tactic.
      std::cout << "Hahah Just checking something" << std::endl;

      z3::solver hahaha_oct(ctx);
      for(auto const & assertion : oct_solver.assertions())
        if(assertion.id() != last_formula_added.id())
          hahaha_oct.add(assertion);
      std::cout << "This must be satisfiable" << std::endl;
      std::cout << (hahaha_oct.check() == z3::sat) << std::endl;

      z3::solver hahaha_euf(ctx);
      for(auto const & assertion : euf_solver.assertions())
        hahaha_euf.add(assertion);
      std::cout << "This must be satisfiable" << std::endl;
      std::cout << (hahaha_euf.check() == z3::sat) << std::endl;
      // *+*+*+*+*+*+*+*+*+*+*+*+*+*+*+*+*+*+*+*+*+*+*+*+*+*+*+*+
#endif

      return;
    }
    oct_solver.pop();

    euf_solver.push();
    if(euf_solver.check() == z3::unsat){
      DEBUG_LOOP_MSG("EUF solver found a contradiction" << std::endl);
      DEBUG_LOOP_MSG(euf_solver.assertions() << std::endl);
     
      z3::expr_vector euf_assertions(ctx);
      for(auto const & assertion : euf_solver.assertions())
        euf_assertions.push_back(assertion);
      CDCL_T cdcl_euf(euf_assertions, EUF);
      cdcl_euf.toDimacsFile();
      PicoProofFactory resolution_proof = PicoProofFactory();
      partialInterpolantNonConvex(
          cdcl_euf,
          resolution_proof,
          ctx.bool_val(false),
          euf_assertions.size(), EUF);
      z3::expr_vector existential_quants(ctx);
      for(unsigned _i = 0; _i < phi.ab_mixed_index; ++_i)
        existential_quants.push_back(ctx.int_const(
              (PREFIX_AB_TEMP_TERM + std::to_string(_i)).c_str()));
      computed_interpolant = z3::exists(existential_quants,
          partial_interpolants.find(ctx.bool_val(false))).simplify();
      DEBUG_LOOP_MSG(
          "-> Final Interpolant: " 
          << computed_interpolant
          << std::endl);
      // This should be allowed 
      // when lift procedures are 
      // given for all the 
      // theories involved
#if 0 
      // *+*+*+*+*+*+*+*+*+*+*+*+*+*+*+*+*+*+*+*+*+*+*+*+*+*+*+*+
      // TODO: get all the witness terms introduced
      // and obtain their representatives (these should be common)
      // Eliminate the witness terms using the solve-eqs tactic.
      std::cout << "Hahah Just checking something" << std::endl;

      z3::solver hahaha_oct(ctx);
      for(auto const & assertion : oct_solver.assertions())
        hahaha_oct.add(assertion);
      std::cout << "This must be satisfiable" << std::endl;
      std::cout << (hahaha_oct.check() == z3::sat) << std::endl;

      z3::solver hahaha_euf(ctx);
      for(auto const & assertion : euf_solver.assertions())
        if(assertion.id() != last_formula_added.id())
          hahaha_euf.add(assertion);
      std::cout << "This must be satisfiable" << std::endl;
      std::cout << (hahaha_euf.check() == z3::sat) << std::endl;
      // *+*+*+*+*+*+*+*+*+*+*+*+*+*+*+*+*+*+*+*+*+*+*+*+*+*+*+*+
#endif

      return;
    }
    euf_solver.pop();
    // ----------------------------------------------------------------
    
    // TODO: add a "solvers' <- state(solvers)" instruction or equivalent here

    // ------------------------------------------------------------------
    // Modify solvers with current_disj_eqs 
    auto current_disj_eqs_form = *current_disj_eqs;
    euf_solver.push();
    euf_solver.add(not(current_disj_eqs_form));
    if(euf_solver.check() == z3::unsat){
      oct_solver.push();
      oct_solver.add(not(current_disj_eqs_form));
      // Case |-_{EUF} current_disj_eqs \land |-_{OCT} current_disj_eqs
      if(oct_solver.check() == z3::unsat){
        euf_solver.pop();
        oct_solver.pop();
        ++current_disj_eqs;
        continue;
      }

      // Case |-_{EUF} current_disj_eqs \land not |-_{OCT} current_disj_eqs
      euf_solver.pop();
      oct_solver.pop();

      DEBUG_LOOP_MSG(std::endl << "Disjunction implied in EUF: "
        << current_disj_eqs_form
        << std::endl);
      
      // These assertions include the original assertions
      z3::expr_vector euf_assertions(ctx);
      for(auto const & assertion : euf_solver.assertions())
        euf_assertions.push_back(assertion);
      // and the negations of each disjunct in current_disj_eqs_form
      // as a conjunct
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

      if(!partial_interpolants.contains(current_disj_eqs_form)){
        CDCL_T cdcl_euf(euf_assertions, EUF);
        cdcl_euf.toDimacsFile();
        PicoProofFactory resolution_proof = PicoProofFactory();
        partialInterpolantNonConvex(
            cdcl_euf, 
            resolution_proof, 
            current_disj_eqs_form, 
            euf_assertions.size(), EUF);
      }
#if _DEBUG_TH_COMB_
      else
        std::cout 
          << "Partial interpolant already computed" << std::endl;
#endif

      last_formula_added = current_disj_eqs_form;
      oct_solver.add(current_disj_eqs_form);
      current_disj_eqs = phi.begin();
      continue;
    }

    oct_solver.push();
    oct_solver.add(not(current_disj_eqs_form));
    // Case not |-_{EUF} current_disj_eqs \land |-_{OCT} current_disj_eqs
    if(oct_solver.check() == z3::unsat){
      euf_solver.pop();
      oct_solver.pop();

      DEBUG_LOOP_MSG(std::endl << "Disjunction implied in OCT: "
        << current_disj_eqs_form
        << std::endl);

      // These assertions include the original assertions
      z3::expr_vector oct_assertions(ctx);
      for(auto const & assertion : oct_solver.assertions())
        oct_assertions.push_back(assertion);
      // and the negations of each disjunct in current_disj_eqs_form
      // as a conjunct
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


      if(!partial_interpolants.contains(current_disj_eqs_form)){
        CDCL_T cdcl_oct(oct_assertions, OCT);
        cdcl_oct.toDimacsFile();
        PicoProofFactory resolution_proof = PicoProofFactory();
        partialInterpolantNonConvex(
            cdcl_oct, 
            resolution_proof, 
            current_disj_eqs_form,
            oct_assertions.size(), OCT);
      }
#if _DEBUG_TH_COMB_
      else
        std::cout << "Partial interpolant already "
          "computed" << std::endl;
#endif

      last_formula_added = current_disj_eqs_form;
      euf_solver.add(current_disj_eqs_form);
      current_disj_eqs = phi.begin();
      continue;
    }

    // Case not |-_{EUF} current_disj_eqs \land not |-_{OCT} current_disj_eqs
    euf_solver.pop();
    oct_solver.pop();
    ++current_disj_eqs;
    // ------------------------------------------------------------------
  } 

#if _DEBUG_TH_COMB_
  std::cout << "The input-formula is satisfiable" << std::endl;
#endif
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

void ThCombInterpolator::checkImpliedEqualities(z3::expr_vector const & terms, z3::solver & s){
  unsigned num_terms = terms.size();
  unsigned class_ids[num_terms];

  for(unsigned i = 0; i < num_terms; i++)
    class_ids[i] = 0;

  switch(s.check_implied_equalities(num_terms, (z3::expr_vector &)terms, class_ids)){
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

void ThCombInterpolator::partialInterpolantConflict(
    z3::expr const & predicate, 
    z3::expr_vector const & conflict_lits, 
    z3::expr_map & local_partial_interp, 
    Theory th){

  z3::expr_vector part_a(ctx);
  z3::expr_vector part_b(ctx);

  DEBUG_CONFLICT_MSG("Inside partialInterpolantConflict" << std::endl);
  
  switch(th){
    case EUF:
      {
        // For loop to separate A-part and B-part
        // respectively
        for(auto const & conflict : conflict_lits){
          if(conflict.is_a_pure()){
            if(conflict.is_not())
              // Turning (not (= a b)) into (distinct a b)
              part_a.push_back(conflict.arg(0).arg(0) != conflict.arg(0).arg(1));
            else
              part_a.push_back(conflict);
          }
          else
            part_b.push_back(conflict);
        }

        DEBUG_CONFLICT_MSG("Part a: ");
        DEBUG_CONFLICT_MSG(part_a << std::endl);
        DEBUG_CONFLICT_MSG("Part b: ");
        DEBUG_CONFLICT_MSG(part_b << std::endl);

        z3::solver s_temp(ctx, "QF_UF");
        if(s_temp.check(part_a) == z3::unsat){
          local_partial_interp.insert(predicate, ctx.bool_val(false));
          return;
        }

        try {
          z3::expr euf_i = z3::mk_and(
              EUFInterpolant(part_a).getInterpolant());
          DEBUG_CONFLICT_MSG("Theory-specific Interpolant for EUF: " << euf_i << std::endl);
          for(auto const & form_a : part_a)
            if(local_partial_interp.contains(form_a))
              euf_i = euf_i || local_partial_interp.find(form_a);
          for(auto const & form_b : part_b)
            if(local_partial_interp.contains(form_b))
              euf_i = euf_i && local_partial_interp.find(form_b);
          DEBUG_CONFLICT_MSG("Interpolant for EUF: " << euf_i << std::endl);
          local_partial_interp.insert(predicate, euf_i.simplify());
          return;
        }
        catch(char const * e){
          throw "Error @ ThCombInterpolator::partial"
            "InterpolantConflict EUF case.";
        }
      }
    case OCT:
      {
        // For loop to separate A-part and B-part
        // respectively
        z3::goal oct_goals(ctx);
        for(auto const & conflict : conflict_lits){
          if(conflict.is_a_pure()){
            part_a.push_back(conflict);
            if(conflict.is_not()){
              auto const & pos_part = conflict.arg(0);
              switch(pos_part.decl().decl_kind()){
                case Z3_OP_EQ:
                  oct_goals.add(OctagonTerm(pos_part.arg(0) != pos_part.arg(1), true).toZ3());
                  break;
                case Z3_OP_DISTINCT:
                  oct_goals.add(OctagonTerm(pos_part.arg(0) == pos_part.arg(1), true).toZ3());
                  break;
                case Z3_OP_GE:
                  oct_goals.add(OctagonTerm(pos_part.arg(0) < pos_part.arg(1), true).toZ3());
                  break;
                case Z3_OP_LE:
                  oct_goals.add(OctagonTerm(pos_part.arg(0) > pos_part.arg(1), true).toZ3());
                  break;
                case Z3_OP_GT:
                  oct_goals.add(OctagonTerm(pos_part.arg(0) <= pos_part.arg(1), true).toZ3());
                  break;
                case Z3_OP_LT:
                  oct_goals.add(OctagonTerm(pos_part.arg(0) <= pos_part.arg(1), true).toZ3());
                  break;
                default:
                  throw "Not an octagonal formula";
              }
            }
            else
              oct_goals.add(OctagonTerm(conflict, true).toZ3());
          }
          else
            part_b.push_back(conflict);
        }
        
        z3::solver s_temp(ctx, "QF_LIA");
        if(s_temp.check(part_a) == z3::unsat){
          DEBUG_CONFLICT_MSG("-------It was unsat" << std::endl);
          local_partial_interp.insert(predicate, ctx.bool_val(false));
          return;
        }

        DEBUG_CONFLICT_MSG("-------It was sat!" << std::endl);
        auto oct_dnf = z3::repeat(
            z3::tactic(ctx, "split-clause") | z3::tactic(ctx, "skip"))(oct_goals);
        z3::expr_vector conjuncts(ctx);
        for(unsigned _i = 0; _i < oct_dnf.size(); _i++) 
          conjuncts.push_back(oct_dnf[_i].as_expr());
        DEBUG_CONFLICT_MSG("DNF: " << z3::mk_or(conjuncts) << std::endl);

        try {
          z3::expr_vector disj_interpolants(ctx);
          for(auto const & conjunct : conjuncts){
            z3::expr_vector oct_input(ctx);
            assert(oct_input.empty());
            for(unsigned _i = 0; _i < conjunct.num_args(); _i++)
              oct_input.push_back(conjunct.arg(_i));

            DEBUG_CONFLICT_MSG("Input for OctagonInterpolant " << oct_input << std::endl);
            disj_interpolants.push_back(z3::mk_and(OctagonInterpolant(oct_input).getInterpolant()));
          }

          z3::expr euf_i = z3::mk_or(disj_interpolants);
          DEBUG_CONFLICT_MSG("Theory-specific interpolant: " 
              << euf_i << std::endl);
          for(auto const & form_a : part_a)
            if(local_partial_interp.contains(form_a))
              euf_i = euf_i || local_partial_interp.find(form_a);
          for(auto const & form_b : part_b)
            if(local_partial_interp.contains(form_b))
              euf_i = euf_i && local_partial_interp.find(form_b);
          DEBUG_CONFLICT_MSG("Interpolant for OCT: " << euf_i << std::endl);
          local_partial_interp.insert(predicate, euf_i.simplify());
          return;
        }
        catch(char const * e){
          throw "Error @ ThCombInterpolator::partial"
            "InterpolantConflict OCT case.";
        }

      }
    case ALL:
      throw "Error @ ThCombInterpolator::partialInterpolantConflict"
        "is only available for single theories.";
  }
}

void ThCombInterpolator::partialInterpolantNonConvex(CDCL_T & cdcl_t, 
    PicoProofFactory const & pf, z3::expr const & formula, 
    unsigned original_num_facts, Theory th){

  unsigned id        = 0;
  z3::expr_map local_partial_interp(ctx);
  z3::expr_vector predicates(ctx);
  z3::expr predicate = ctx.bool_val(true);

  for(auto const & res_proof : pf.proof_table){
    bool is_fact = res_proof.subproof_1 == -1 && res_proof.subproof_2 == -1;

    // Skip element in proof table if it is not defined
    if(res_proof.size() == 0 && is_fact) {
      id++;
      predicates.push_back(ctx.bool_val(true));
      continue; 
    }
    // -------------------------------------------------------------------------------
    // Obtain predicate
    z3::expr_vector clause_lits(ctx);
    z3::expr_vector conflict_lits(ctx);
    for(auto const & literal : res_proof){
      if(literal < 0){
        clause_lits.push_back(not(cdcl_t.concretizeAbstraction(-literal)));
        conflict_lits.push_back(cdcl_t.concretizeAbstraction(-literal));
      }
      else{
        clause_lits.push_back(cdcl_t.concretizeAbstraction(literal));
        conflict_lits.push_back(not(cdcl_t.concretizeAbstraction(literal)));
      }
    }
    if(res_proof.size() == 0)
      predicate = ctx.bool_val(false);
    else if(res_proof.size() == 1)
      predicate = clause_lits[0];
    else
      predicate = z3::mk_or(clause_lits);
    // -------------------------------------------------------------------------------
    predicates.push_back(predicate);


    DEBUG_NON_CONV_MSG("Clause Id: " << id);

    if(is_fact){
      if(id <= original_num_facts){
        DEBUG_NON_CONV_MSG(" (Fact) Predicate: " << predicate);
        if(partial_interpolants.contains(predicate)){
          // This step ensure that the local maps contains
          // previous interpolants from processed facts
          local_partial_interp.insert(predicate, partial_interpolants.find(predicate));
          DEBUG_NON_CONV_MSG(" Interpolant(old): " << partial_interpolants.find(predicate) << std::endl);
        }
        else{
          // ------------------------------------------------------------
          // Compute local base case interpolant
          if(predicate.is_a_pure()){
            local_partial_interp.insert(predicate, ctx.bool_val(false));
            DEBUG_NON_CONV_MSG(" Interpolant(new): false" << std::endl);
          }
          else{
            local_partial_interp.insert(predicate, ctx.bool_val(true));
            DEBUG_NON_CONV_MSG(" Interpolant((from fact/input)new): true" << std::endl);
          }
          // ------------------------------------------------------------
        }
      }
      else{
        DEBUG_NON_CONV_MSG(" (Conflict Clause) Predicate: " << predicate << std::endl);
        if(partial_interpolants.contains(predicate)){
          local_partial_interp.insert(predicate, partial_interpolants.find(predicate));
          DEBUG_NON_CONV_MSG(
              "Interpolant(old): " << partial_interpolants.find(predicate) << std::endl
              );
        }
        else{
          // Compute local conflict interpolant
          partialInterpolantConflict(predicate, conflict_lits, local_partial_interp, th);
          DEBUG_NON_CONV_MSG(
              "Interpolant((from conflict)new): " 
              << local_partial_interp.find(predicate) 
              << std::endl
              );
        }
      }
    }
    else{
      assert(res_proof.pivot > 0);
      z3::expr pivot_form = cdcl_t.concretizeAbstraction(res_proof.pivot);
      DEBUG_NON_CONV_MSG(
          " (Derived(" << std::to_string(res_proof.subproof_1) 
          << "," << std::to_string(res_proof.subproof_2) << "))"
          << " Predicate: " << predicate
          << " Pivot: " << pivot_form << std::endl
          );

      if(partial_interpolants.contains(predicate)){
        local_partial_interp.insert(predicate, partial_interpolants.find(predicate));
        DEBUG_NON_CONV_MSG(
            "Interpolant(old): " 
            << partial_interpolants.find(predicate) 
            << std::endl
            );
      }
      else{
        // Compute local resolution interpolant
        if(pivot_form.is_a_strict()){ // Pivot is A-local
          DEBUG_NON_CONV_MSG("Pivot is A-local" << std::endl);
          DEBUG_NON_CONV_MSG("Partial interpolant " 
              <<
              (local_partial_interp.find(predicates[res_proof.subproof_1]) 
               || local_partial_interp.find(predicates[res_proof.subproof_2]))
              << std::endl
              );
          local_partial_interp.insert(predicate, 
              (local_partial_interp.find(predicates[res_proof.subproof_1]) 
               || local_partial_interp.find(predicates[res_proof.subproof_2])).simplify());
        }
        else if(pivot_form.is_b_strict()){ // Pivot is B-local
          DEBUG_NON_CONV_MSG("Pivot is B-local" << std::endl);
          DEBUG_NON_CONV_MSG("Partial interpolant "
              <<
              (local_partial_interp.find(predicates[res_proof.subproof_1]) 
               && local_partial_interp.find(predicates[res_proof.subproof_2]))
              << std::endl;
              );
          local_partial_interp.insert(predicate, 
              (local_partial_interp.find(predicates[res_proof.subproof_1]) 
               && local_partial_interp.find(predicates[res_proof.subproof_2])).simplify());
        }
        else{ // Pivot is AB-common
          // TODO: fix proper matching of pivot with the partial interpolants
          // i.e. if c = res_x(c1, c2), c1 = x \lor c1', and c2 = \not x \lor c2'
          // then p(c) = (p(c1) \lor x) \land (p(c2) \lor \not x)
          // currently the output can be (p(c1) \lor \not x) \land (p(c2) \lor x)
          // since the code doesn't check this condition
          DEBUG_NON_CONV_MSG("Pivot is AB-common" << std::endl);
          z3::expr actual_pivot = pivot_form;
          if(!pf.proof_table[res_proof.subproof_1].containsPivot(res_proof.pivot)){
            actual_pivot = not(actual_pivot);
          }

          DEBUG_NON_CONV_MSG("Partial interpolant: " 
              <<
              ((actual_pivot || local_partial_interp.find(predicates[res_proof.subproof_1])) 
               && 
               (not(actual_pivot)|| local_partial_interp.find(predicates[res_proof.subproof_2]))) 
              << std::endl
              );
          local_partial_interp.insert(predicate, 
              ((actual_pivot || local_partial_interp.find(predicates[res_proof.subproof_1])) 
               && 
               (not(actual_pivot) || local_partial_interp.find(predicates[res_proof.subproof_2]))).simplify());
        }
        DEBUG_NON_CONV_MSG(
            "Interpolant((from derived)new): " 
            << local_partial_interp.find(predicate) 
            << std::endl
            );
      }
    }

    id++;
  }

  DEBUG_NON_CONV_MSG(
      "Final interpolant for conflict clause: " 
      << local_partial_interp.find(ctx.bool_val(false))
      << std::endl
      );
  partial_interpolants.insert(formula, 
      local_partial_interp.find(ctx.bool_val(false)).simplify());
}

void ThCombInterpolator::getInterpolant(){
}

std::ostream & operator << (std::ostream & os, ThCombInterpolator & p){
  return os << "The interpolant is: " << p.computed_interpolant;
}
