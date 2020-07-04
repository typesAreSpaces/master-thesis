#include "CDCL_T.h"

CDCL_T::CDCL_T(z3::expr_vector const & formulas) :
  abstraction_fresh_index(1),
  ctx(formulas.ctx()), input(formulas),
  prop_solver(ctx), theory_solver(ctx),
  abstractions(ctx), concretes(ctx),
  abstract_conflict_clauses(ctx)
{
#if _DEBUG_CDCL_T_
  std::cout << "Original formulas" << std::endl;
  std::cout << input << std::endl;
#endif
  try {
    // Setup prop solver
    for(auto const & abstract_clause : abstract_clauses(formulas))
      prop_solver.add(abstract_clause);
    // Setup theory solver
    for(auto const & predicate : abstractions.keys())
      theory_solver.add(predicate == abstractions.find(predicate));
    // Find conflict-clauses
    loop();
#if _DEBUG_CDCL_T_
    std::cout << "--Conflict clauses found" << std::endl; 
    std::cout << abstract_conflict_clauses << std::endl << std::endl;
#endif
  }
  catch(char const * e){
    std::cout << e << std::endl;
  }
#if _DEBUG_CDCL_T_
  std::cout << "--Abstractions" << std::endl;
  for(auto const & key : abstractions.keys())
    std::cout << key << " |-> " << abstractions.find(key) << std::endl;
  std::cout << std::endl;
#endif
}

z3::expr CDCL_T::abstract_atom(z3::expr const & atom){
  if(abstractions.contains(atom))
    return abstractions.find(atom);
  z3::expr abstract_atom = ctx.bool_const(("__p" + std::to_string(abstraction_fresh_index++)).c_str());
  abstractions.insert(atom, abstract_atom);
  concretes.insert(abstract_atom, atom);
  return abstract_atom;
}

z3::expr CDCL_T::abstract_lit(z3::expr const & lit){
  if(lit.is_not())
    return not(abstract_atom(lit.arg(0)));
  if(lit.is_distinct())
    return not(abstract_atom(lit.arg(0) == lit.arg(1)));
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
      result.push_back(abstract_lit);
    else
      result.push_back(not(abstract_lit));
  }
  return result;
}

void CDCL_T::loop(){
  while(true){
    auto is_sat = prop_solver.check();
    if(z3::sat == is_sat){
      z3::model partial_model = prop_solver.get_model();
      if(z3::unsat == theory_solver.check(mk_lits(partial_model))){
        auto unsat_cores = theory_solver.unsat_core();
        prop_solver.add(not(z3::mk_and(unsat_cores)));
        // -------------------------------------------------------
        // Track conflic clauses
        if(unsat_cores.size() == 1){
          z3::expr conflict_clause = unsat_cores[0];
          if(conflict_clause.is_not())
            abstract_conflict_clauses.push_back(conflict_clause.arg(0));
          else
            abstract_conflict_clauses.push_back(not(conflict_clause));
        }
        else{
          z3::expr_vector conflict_clause(ctx);
          for(auto const & unsat_core : unsat_cores){
            if(unsat_core.is_not())
              conflict_clause.push_back(unsat_core.arg(0));
            else
              conflict_clause.push_back(not(unsat_core));
          }
          abstract_conflict_clauses.push_back(z3::mk_or(conflict_clause));
        }
        // -------------------------------------------------------
      }
#if _DEBUG_CDCL_T_
      else{
        std::cout << "Result: sat" << std::endl;
        std::cout << "Model: \n" << theory_solver.get_model() << std::endl;
      }
#endif
    }
    else{
#if _DEBUG_CDCL_T_
      std::cout << "Result: unsat" << std::endl;
#endif
      return;
    }
  }
}

z3::expr_vector const CDCL_T::getConflictClauses() const {
  return abstract_conflict_clauses;
}

std::ofstream & CDCL_T::dimacsLit(std::ofstream & file, z3::expr const & abstract_lit){
  if(abstract_lit.is_not()){
    auto const & abstract_name = abstract_lit.arg(0).decl().name().str();
    file << "-" 
      << (unsigned)std::stol(abstract_name.substr(3, abstract_name.size() - 1)) 
      << " ";
    return file;
  }
  auto const & abstract_name = abstract_lit.decl().name().str();
  file 
    << (unsigned)std::stol(abstract_name.substr(3, abstract_name.size() - 1)) 
    << " ";
  return file;
}

std::ofstream & CDCL_T::dimacsClause(std::ofstream & file, z3::expr const & abstract_e){
  if(abstract_e.is_app()){
    switch(abstract_e.decl().decl_kind()){
      case Z3_OP_OR:
        {
          unsigned num_args = abstract_e.num_args();
          for(unsigned _i = 0; _i < num_args; ++_i)
            dimacsLit(file, abstract_e.arg(_i));
          break;
        }
      case Z3_OP_NOT:
      case Z3_OP_UNINTERPRETED:
        dimacsLit(file, abstract_e);
        break;
      default:
        throw "There is a problem";
    }
    return file;
  }
  throw "Not a function appication.";
}

void CDCL_T::toDimacsFile(){
  std::ofstream out;
  out.open("file.cnf");
  out << "p cnf " 
    << (abstraction_fresh_index-1) << " " 
    << input.size() + abstract_conflict_clauses.size() << std::endl;  
  for(auto const & abstract_clause : abstract_clauses(input)){
#if _DEBUG_CDCL_T_
    std::cout << abstract_clause << std::endl;
#endif
    dimacsClause(out, abstract_clause) << "0" << std::endl;
  }
  for(auto const & clause : abstract_conflict_clauses){
#if _DEBUG_CDCL_T_
    std::cout << clause << std::endl;
#endif
    dimacsClause(out, clause) << "0" << std::endl;
  }
  out.close();
  return;
}

std::ostream & operator << (std::ostream & os, CDCL_T const & cdcl){
  return os;
}
