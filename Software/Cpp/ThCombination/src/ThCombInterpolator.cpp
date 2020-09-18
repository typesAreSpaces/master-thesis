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
  original_part_a_ids({}), original_part_b_ids({}),
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

  for(auto const & _form : part_a.getOctComponent()){
    z3::expr form = _form;
    if(form.is_distinct())
      form = !(_form.arg(0) == _form.arg(1));
    oct_solver.add(form);
    original_part_a_ids.insert(form.id());
    partial_interpolants.insert(form, ctx.bool_val(false));
    DEBUG_LOOP_MSG(form << std::endl);
  }
  for(auto const & _form : part_b.getOctComponent()){
    z3::expr form = _form;
    if(form.is_distinct())
      form = !(_form.arg(0) == _form.arg(1));
    oct_solver.add(form);
    original_part_b_ids.insert(form.id());
    partial_interpolants.insert(form, ctx.bool_val(true));
    DEBUG_LOOP_MSG(form << std::endl);
  }
  for(auto const & _form : part_a.getEufComponent()){
    z3::expr form = _form;
    if(form.is_distinct())
      form = !(_form.arg(0) == _form.arg(1));
    euf_solver.add(form);
    original_part_a_ids.insert(form.id());
    partial_interpolants.insert(form, ctx.bool_val(false));
    DEBUG_LOOP_MSG(form << std::endl);
  }
  for(auto const & _form : part_b.getEufComponent()){
    z3::expr form = _form;
    if(form.is_distinct())
      form = !(_form.arg(0) == _form.arg(1));
    euf_solver.add(form);
    original_part_b_ids.insert(form.id());
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
          oct_assertions.size(), OCT);

      liftInterpolant(phi);

      DEBUG_LOOP_MSG(
          "-> Final Interpolant: " 
          << computed_interpolant
          << std::endl);
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

      liftInterpolant(phi);

      DEBUG_LOOP_MSG(
          "-> Final Interpolant: " 
          << computed_interpolant
          << std::endl);
      return;
    }
    euf_solver.pop();
    // ----------------------------------------------------------------

    // ------------------------------------------------------------------
    // Modify solvers with current_disj_eqs 
    auto current_disj_eqs_form = *current_disj_eqs;
#if _DEBUG_TH_COMB_
    std::cout << "Current disjunction: " << current_disj_eqs_form << std::endl;
#endif
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

      // These assertions include the original current assertions
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

      // These assertions include the original current assertions
      z3::expr_vector oct_assertions(ctx);
      for(auto const & assertion : oct_solver.assertions())
        oct_assertions.push_back(assertion);
      // and the negations of each disjunct in current_disj_eqs_form
      // as a conjunct
      if(current_disj_eqs_form.decl().decl_kind() == Z3_OP_OR){
        unsigned num_arg_disj = current_disj_eqs_form.num_args();
        for(unsigned _i = 0; _i < num_arg_disj; ++_i)
          oct_assertions.push_back(not(current_disj_eqs_form.arg(_i)));
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
        DEBUG_CONFLICT_MSG("Case EUF" << std::endl);
        // For loop to separate A-part and B-part
        // respectively
        for(auto const & conflict : conflict_lits){
          auto const & in_a_part = inSet(conflict.id(), original_part_a_ids);
          auto const & in_b_part = inSet(conflict.id(), original_part_b_ids);
          //if(conflict.is_a_pure()){
          if((!in_a_part && !in_b_part && conflict.is_a_pure()) || in_a_part){
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
          DEBUG_CONFLICT_MSG("Case OCT" << std::endl);
          DEBUG_CONFLICT_MSG("Conflict lits: " << conflict_lits << std::endl);

          // For loop to separate A-part and B-part
          // respectively
          z3::goal oct_goals(ctx);
          for(auto const & conflict : conflict_lits){
            auto const & in_a_part = inSet(conflict.id(), original_part_a_ids);
            auto const & in_b_part = inSet(conflict.id(), original_part_b_ids);
#if _DEBUG_TH_COMB_
            std::cout << "Stats about this conflict: " << conflict << std::endl;
            std::cout << "in_a_part: " << in_a_part << std::endl;
            std::cout << "in_b_part: " << in_b_part << std::endl;
            std::cout << "is_a_pure: " << conflict.is_a_pure() << std::endl;
#endif
            if((!in_a_part && !in_b_part && conflict.is_a_pure()) || in_a_part){
              part_a.push_back(conflict);
              // ------------------------------------------------------------------------
#if NEW_APPROACH
              if(isPurifiedEquality(conflict)){
                oct_goals.add(conflict.arg(0) <= conflict.arg(1));
                oct_goals.add(conflict.arg(1) <= conflict.arg(0));
                oct_goals.add(conflict);
              }
              else
                oct_goals.add(conflict);
#else
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
                    oct_goals.add(OctagonTerm(pos_part.arg(0) >= pos_part.arg(1), true).toZ3());
                    break;
                  default:
                    throw "Not an octagonal formula";
                }
              }
              else
                oct_goals.add(OctagonTerm(conflict, true).toZ3());
#endif
              // ------------------------------------------------------------------------
            }
            else
              part_b.push_back(conflict);
          }

          DEBUG_CONFLICT_MSG("Part a: " << part_a << std::endl);
          DEBUG_CONFLICT_MSG("Part b: " << part_b << std::endl);

#if NEW_APPROACH
          z3::apply_result solved_eqs = z3::tactic(ctx, "solve-eqs")(oct_goals);
#if _DEBUG_TH_COMB_
          std::cout << "Before Solved eqs " << oct_goals << std::endl;
          std::cout << "Solved eqs " << solved_eqs << std::endl;
#endif
          assert(solved_eqs.size() == 1);
          z3::expr solved_conj_eqs = solved_eqs[0].as_expr();
          if(solved_conj_eqs.bool_value() == true){
            z3::expr_vector temp_goals_(ctx);
            for(unsigned _i = 0; _i < oct_goals.size(); _i++)
              temp_goals_.push_back(oct_goals[_i]);
            solved_conj_eqs = z3::mk_and(temp_goals_);
          }
#if _DEBUG_TH_COMB_
          std::cout << "Solved conj eqs: " << solved_conj_eqs << std::endl;
#endif
          z3::goal propagated_oct_goals(ctx);
          if(solved_conj_eqs.is_and())
            for(unsigned _i = 0; _i < solved_conj_eqs.num_args(); _i++)
              updateOctGoals(solved_conj_eqs.arg(_i), propagated_oct_goals);
          else
            updateOctGoals(solved_conj_eqs, propagated_oct_goals);
#endif

          z3::solver s_temp(ctx, "QF_LIA");
          if(s_temp.check(part_a) == z3::unsat){
            DEBUG_CONFLICT_MSG("-------It was unsat" << std::endl);
            local_partial_interp.insert(predicate, ctx.bool_val(false));
            return;
          }

          DEBUG_CONFLICT_MSG("-------It was sat!" << std::endl);

          auto oct_dnf = z3::repeat(
              z3::tactic(ctx, "split-clause") | z3::tactic(ctx, "skip"))(propagated_oct_goals);
          z3::expr_vector conjuncts(ctx);
          for(unsigned _i = 0; _i < oct_dnf.size(); _i++) 
            conjuncts.push_back(oct_dnf[_i].as_expr());
          DEBUG_CONFLICT_MSG("DNF: " << z3::mk_or(conjuncts) << std::endl);

          try {
            z3::expr_vector disj_interpolants(ctx);
            for(auto const & conjunct : conjuncts){
              z3::expr_vector oct_input(ctx);
              assert(oct_input.empty());

              if(conjunct.decl().decl_kind() == Z3_OP_AND)
                for(unsigned _i = 0; _i < conjunct.num_args(); _i++)
                  oct_input.push_back(conjunct.arg(_i));
              else
                oct_input.push_back(conjunct);


              DEBUG_CONFLICT_MSG("Input for OctagonInterpolant " << oct_input << std::endl);
              disj_interpolants.push_back(z3::mk_and(OctagonInterpolant(oct_input).getInterpolant()));
            }

            z3::expr oct_i = z3::mk_or(disj_interpolants);
            DEBUG_CONFLICT_MSG("Theory-specific interpolant: " 
                << oct_i << std::endl);
            for(auto const & form_a : part_a)
              if(local_partial_interp.contains(form_a))
                oct_i = oct_i || local_partial_interp.find(form_a);
            for(auto const & form_b : part_b)
              if(local_partial_interp.contains(form_b))
                oct_i = oct_i && local_partial_interp.find(form_b);
            DEBUG_CONFLICT_MSG("Interpolant for OCT: " << oct_i << std::endl);
            local_partial_interp.insert(predicate, oct_i.simplify());
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
      // Obtain predicates
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

  void ThCombInterpolator::liftInterpolant(DisjEqsPropagator const & phi){
    if(phi.ab_mixed_index){
      z3::expr_vector existential_quants(ctx);
      for(unsigned _i = 0; _i < phi.ab_mixed_index; ++_i)
        existential_quants.push_back(ctx.int_const(
              (PREFIX_AB_TEMP_TERM + std::to_string(_i)).c_str()));
      computed_interpolant = z3::exists(existential_quants,
          partial_interpolants.find(ctx.bool_val(false))).simplify();
    }
    else
      computed_interpolant = partial_interpolants.find(ctx.bool_val(false)).simplify();

    computed_interpolant = computed_interpolant
      .substitute(part_a.persistent_to, part_a.persistent_from)
      .substitute(part_b.persistent_to, part_b.persistent_from)
      .simplify();
  }

  bool ThCombInterpolator::isPurifiedEquality(z3::expr const & e) const {
    if(e.is_eq()){
      std::string euf_prefix;
      std::string oct_prefix;
      std::string lhs_name = e.arg(1).decl().name().str(); 
      // TODO: add more if more theories are added!
#if ADD_COMMON_PREFIX
      euf_prefix = PREFIX_COMM_EUF;
      oct_prefix = PREFIX_COMM_OCT;
#else
      euf_prefix = PREFIX_EUF;
      oct_prefix = PREFIX_OCT;
#endif
      return 
        (std::mismatch(euf_prefix.begin(), euf_prefix.end(), lhs_name.begin()).first == euf_prefix.end())
        || (std::mismatch(oct_prefix.begin(), oct_prefix.end(), lhs_name.begin()).first == oct_prefix.end());
    }
    return false;
  }

  void ThCombInterpolator::updateOctGoals(z3::expr const & conflict, z3::goal & oct_goals){
#if _DEBUG_TH_COMB_
    std::cout << "Current conflict " << conflict << std::endl;
#endif
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
          oct_goals.add(OctagonTerm(pos_part.arg(0) >= pos_part.arg(1), true).toZ3());
          break;
        default:
          throw "Not an octagonal formula";
      }
    }
    else
      oct_goals.add(OctagonTerm(conflict, true).toZ3());
    return;
  }

  z3::expr ThCombInterpolator::getInterpolant() const {
    return computed_interpolant;
  }

  std::ostream & operator << (std::ostream & os, ThCombInterpolator & p){
    return os << "The interpolant is: " << p.computed_interpolant;
  }
