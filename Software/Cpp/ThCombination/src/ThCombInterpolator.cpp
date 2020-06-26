#include "ThCombInterpolator.h"
#include <z3++.h>
#define _DEBUGEXTPURIFIER_ false

ThCombInterpolator::ThCombInterpolator(z3::context & ctx,
    z3::expr_vector const & formula_a, z3::expr_vector const & formula_b) :
  ctx(ctx), 
  part_a(formula_a), part_b(formula_b),
  euf_solver(ctx, "QF_UF"), oct_solver(ctx, "QF_LIA"),
  shared_variables(ctx), partial_interpolants(ctx)
{

  // Keep working here

  // Find theory that unsat by passing 
  // disjuntions of equalities
  
  std::cout << "Part a" << std::endl;
  std::cout << part_a;
  std::cout << "Shared variables - a" << std::endl;
  std::cout << part_a.getSharedVariables() << std::endl;
  std::cout << "Part b" << std::endl;
  std::cout << part_b;
  std::cout << "Shared variables - b" << std::endl;
  std::cout << part_b.getSharedVariables() << std::endl;

  for(auto const & shared_var : part_a.getSharedVariables())
    shared_variables.push_back(shared_var);
  for(auto const & shared_var : part_b.getSharedVariables())
    shared_variables.push_back(shared_var);

  DisjEqsPropagator phi_it(shared_variables);

  z3::solver combined_solver(ctx, "QF_UFLIA");
  for(auto const & form : formula_a)
    combined_solver.add(form);
  for(auto const & form : formula_b)
    combined_solver.add(form);

  // Issue here
  std::cout << "wait wot " << combined_solver.check() << std::endl;
  
  while(combined_solver.check() != z3::unsat){
    std::cout << "Hey keep working here" << std::endl;
    unsigned stop;
    std::cin >> stop;
  }

  //DisjEqsPropagator phi();

  //
  // Using CDCL_T, find conflict clauses
  //
  // Using Z3, find unsat proof 

  // unsigned num = euf_component.size();
  // for(unsigned i = 0; i < num; i++)
 //   euf_solver.add(euf_component[i]);

  // num = oct_component.size();
  // for(unsigned i = 0; i < num; i++)
  //   oct_solver.add(oct_component[i]);
}

ThCombInterpolator::~ThCombInterpolator(){
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

bool ThCombInterpolator::isProvable(z3::solver & s, z3::expr const & e){
  s.push();
  s.add(!e);
  bool answer = s.check() == z3::unsat;
  s.pop();
  return answer;
}

void ThCombInterpolator::addConjunction(z3::solver & s, z3::expr const & e){
  if (e.is_app()) {
    z3::func_decl e_decl = e.decl();
    switch(e_decl.decl_kind()){
      case Z3_OP_AND: // FIX: Arity might not be 2 (?)
        addConjunction(s, e.arg(0));
        addConjunction(s, e.arg(1));
        return;
      default:
        s.add(e);
        return;
    }
  }
  throw "Wrong term";
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

void ThCombInterpolator::printf___(z3::expr const & proof){
  unsigned num = proof.num_args();
  z3::func_decl proof_decl = proof.decl();

  std::cout << proof_decl.name() << ": ";    
  for(unsigned i = 0; i < num - 1; i++){
    unsigned temp_size = proof.arg(i).num_args();
    auto partial_interpolant = partial_interpolants.find(proof.arg(i).arg(temp_size - 1));
    std::cout << proof.arg(i).arg(temp_size - 1) << " ; " 
      << partial_interpolant << ", ";
  }
  auto partial_interpolant = partial_interpolants.find(proof.arg(num - 1));
  std::cout << "|- " << proof.arg(num - 1) << " ; "
    << partial_interpolant << std::endl;
}

// Invariant: Insert a partial interpolant in the consequent of a proof
// before calling printf__
void ThCombInterpolator::traverseProof1(z3::expr const & proof) {
  if(proof.is_app()){
    unsigned num = proof.num_args();
    z3::func_decl proof_decl = proof.decl();
    switch(proof_decl.decl_kind()){
      case Z3_OP_PR_LEMMA:
        {
          // Invariant --------------------------------------------------------
          auto consequent = proof.arg(num - 1);
          partial_interpolants.insert(consequent, partialInterpolantConflictClause());
          //           --------------------------------------------------------
          // Printing -------------------------------
          std::cout << proof_decl.name() << ": ";
          std::cout << "|- " << proof.arg(num - 1) << " ; " 
            << partial_interpolants.find(consequent) << std::endl;
          //          ---------------------
          return;
        }
      case Z3_OP_PR_ASSERTED:
        { // check
          // Invariant ------------------------------------------------
          auto asserted = proof.arg(0);
          if(part_a.inside(asserted))
            partial_interpolants.insert(asserted, ctx.bool_val(false));
          else
            partial_interpolants.insert(asserted, ctx.bool_val(true));
          //           ------------------------------------------------
          // Printing -----
          printf___(proof);
          //          -----
          return;
        }
      case Z3_OP_PR_UNIT_RESOLUTION:
        { // check
          for(unsigned i = 0; i < num - 1; i++)
            traverseProof1(proof.arg(i));

          // Invariant ----------------------------
          unsigned temp_size = proof.arg(0).num_args();
          z3::expr temp_partial_interpolant = 
            partialInterpolantUnitResolution(partial_interpolants.find(proof.arg(0).arg(temp_size - 1)),
              proof.arg(1));
          for(unsigned i = 2; i < num - 1; i++)
            temp_partial_interpolant = 
              partialInterpolantUnitResolution(temp_partial_interpolant, proof.arg(i));
          partial_interpolants.insert(proof.arg(num - 1), temp_partial_interpolant);
          //           ---------------------------
          // Printing -----
          printf___(proof);
          //          -----
          return;
        }
      case Z3_OP_PR_TH_LEMMA:
        {
          for(unsigned i = 0; i < num - 1; i++)
            traverseProof1(proof.arg(i));

          // Invariant -----------------------------------------------------------------
          // WRONG:
          partial_interpolants.insert(proof.arg(num - 1), partialInterpolantConvex());
          //           -----------------------------------------------------------------
          // Printing -----
          printf___(proof);
          //          -----
          return;
        }
      default:
        {
          z3::expr_vector hyps(proof.ctx());
          traverseProof2(proof, hyps);
          // Printing hyps -------------------------------------------------------------
          std::cout << "provable: ";
          unsigned num_hyps = hyps.size();
          for(unsigned i = 0; i < num_hyps; i++)
            std::cout << hyps[i] << " ; " 
              << partial_interpolants.find(hyps[i]) << ", ";
          //          ------------------------------------------------------------------

          auto consequent = proof.arg(num - 1);
          partial_interpolants.insert(consequent, ctx.bool_val(true)); // Wrong! Just momentarily

          // Printing consequent  ---------------
          std::cout << "|- " << proof.arg(num - 1) << " ; " 
            << partial_interpolants.find(consequent) << std::endl;
          //          --------------------------
          return;
        }
    }
  }
  throw "Wrong proof-term in traverseProof1";
}

void ThCombInterpolator::traverseProof2(z3::expr const & proof, z3::expr_vector & hyps) {
  if(proof.is_app()){
    unsigned num = proof.num_args();
    z3::func_decl proof_decl = proof.decl();
    switch(proof_decl.decl_kind()){      
      case Z3_OP_PR_ASSERTED:
      case Z3_OP_PR_LEMMA:
      case Z3_OP_PR_UNIT_RESOLUTION:
      case Z3_OP_PR_TH_LEMMA:
        {
          traverseProof1(proof);
          hyps.push_back(proof.arg(num - 1));
          return;
        }
      default:
        {      
          for(unsigned i = 0; i < num - 1; i++)
            traverseProof2(proof.arg(i), hyps);
          return;
        }
    }
  }
  throw "Wrong proof-term in traverseProof2";
}

void ThCombInterpolator::getInterpolant(){
  // Traverse Proof of QF_UFLIA
}

std::ostream & operator << (std::ostream & os, ThCombInterpolator & p){
  z3::solver aux_solver(p.ctx, "QF_UFLIA");

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
