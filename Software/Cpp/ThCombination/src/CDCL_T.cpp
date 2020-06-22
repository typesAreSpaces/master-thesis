#include "CDCL_T.h"
#include <z3++.h>

CDCL_T::CDCL_T(z3::context & ctx, z3::expr_vector const & formulas) :
  index(0),
  ctx(ctx),
  prop_solver(ctx), theory_solver(ctx),
  abstractions(ctx), concretes(ctx)
{
  try {
    for(auto const & abstract_clause : abstract_clauses(formulas))
      prop_solver.add(abstract_clause);
  }
  catch(char const * e){
    std::cout << e << std::endl;
  }

  for(auto const & clause : formulas)
    theory_solver.add(clause);

  cdcl();
}

z3::expr CDCL_T::abstract_atom(z3::expr const & atom){
  if(abstractions.contains(atom))
    return abstractions.find(atom);
  z3::expr abstract_atom = ctx.bool_const(("p" + std::to_string(index++)).c_str());
  abstractions.insert(atom, abstract_atom);
  concretes.insert(abstract_atom, atom);
  return abstract_atom;
}

z3::expr CDCL_T::abstract_lit(z3::expr const & lit){
  if(lit.is_not())
    return not(abstract_atom(lit.arg(0)));
  return abstract_atom(lit);
}

z3::expr CDCL_T::abstract_clause(z3::expr const & clause){
  auto f = clause.decl().decl_kind();
  switch(f){
    case Z3_OP_OR:
      {
        z3::expr_vector args(ctx);
        unsigned num_args = clause.num_args();
        for(unsigned _i = 0; _i < num_args; ++_i)
          args.push_back(abstract_lit(clause.arg(_i)));
        return z3::mk_or(args);
      }
    case Z3_OP_EQ:
    case Z3_OP_DISTINCT:
    case Z3_OP_LE:    
    case Z3_OP_GE:
    case Z3_OP_LT:
    case Z3_OP_GT:
    case Z3_OP_NOT:
    case Z3_OP_UNINTERPRETED:
      return abstract_lit(clause);
    default:
      throw "Error @ CDCL_T::abstract_lit." 
        "The expression is not a disjunction of "
        "allowed predicates in QF_UF with UTVPI.";
  }
  return clause;
}

z3::expr_vector CDCL_T::abstract_clauses(z3::expr_vector const & clauses){
  z3::expr_vector result(ctx);
  for(auto const & clause : clauses)
    result.push_back(abstract_clause(clause));
  return result;
}

z3::expr_vector CDCL_T::mk_lits(z3::model const & m){
  z3::expr_vector result(ctx);
  for(auto const & abstract_lit : concretes.keys()){
    if(m.eval(abstract_lit).is_true())
      result.push_back(concretes.find(abstract_lit));
    else
      result.push_back(not(concretes.find(abstract_lit)));
  }
  return result;
}

void CDCL_T::block_conflict_clause(z3::expr_vector const & unsat_cores){
  z3::expr_vector result(ctx);
  for(auto const & unsat_core : unsat_cores)
    result.push_back(abstract_lit(unsat_core));
  prop_solver.add(not(z3::mk_and(result)));
}

void CDCL_T::cdcl(){
  while(true){
    auto is_sat = prop_solver.check();
    if(z3::sat == is_sat){
      z3::model partial_model = prop_solver.get_model();
      auto lits               = mk_lits(partial_model);
      if(z3::unsat == theory_solver.check(lits)){
        auto unsat_cores = theory_solver.unsat_core();
        block_conflict_clause(unsat_cores);
        // ------------------------------------------
        // TODO: store the conflict clauses somewhere
        // in order to compute the
        // partial conflict clauses interpolants later
        // -------------------------------------------------
        auto conflict_clause = not(z3::mk_and(unsat_cores));
        std::cout << "Conflict clause found " << conflict_clause << std::endl;
        // -------------------------------------------------------------------
      }
      else{
        std::cout << "Result: sat" << std::endl;
        std::cout << "Model: \n" << theory_solver.get_model() << std::endl;
      }
    }
    else{
      std::cout << "Result: unsat" << std::endl;
      return;
    }
  }
}
