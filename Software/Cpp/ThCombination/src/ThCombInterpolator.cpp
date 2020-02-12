#include "ThCombInterpolator.h"
#define _DEBUGEXTPURIFIER_ false

ThCombInterpolator::ThCombInterpolator(z3::context & ctx,
				       z3::expr const & formula_a, z3::expr const & formula_b) :
  part_a(formula_a), part_b(formula_b),
  euf_solver(ctx, "QF_UF"), oct_solver(ctx, "QF_LIA")
{
  // unsigned num = euf_component.size();
  // for(unsigned i = 0; i < num; i++)
  //   euf_solver.add(euf_component[i]);

  // num = oct_component.size();
  // for(unsigned i = 0; i < num; i++)
  //   oct_solver.add(oct_component[i]);
}

ThCombInterpolator::~ThCombInterpolator(){
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
      case Z3_OP_AND:
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

// void ThCombInterpolator::traverseProof(z3::expr const & proof) {
//   if(earlyExit(visited, proof))
//     return;
    
//   if (proof.is_app()) {
//     unsigned num = proof.num_args();
//     for (unsigned i = 0; i < num; i++) 
//       traverseProof(proof.arg(i));
    
//     z3::func_decl proof_decl = proof.decl();
//     switch(proof_decl.decl_kind()) {
//     case Z3_OP_PR_MONOTONICITY:{
//       auto consequent = proof.arg(num - 1).simplify();
//       auto consequent_kind = consequent.decl().decl_kind();
//       // Avoid visited consequents and anything but equalities
//       if(earlyExit(consequent_visited, consequent) || consequent_kind != Z3_OP_EQ)
// 	return;
//       // Avoid 'high-order equalities'
//       // between {==, !=, <, >, <=, >=}
//       switch(consequent.arg(0).decl().decl_kind()){
//       case Z3_OP_EQ:
//       case Z3_OP_DISTINCT:
//       case Z3_OP_LE:
//       case Z3_OP_GE:
//       case Z3_OP_LT:
//       case Z3_OP_GT:
// 	return;
//       default:{
// 	std::cout << "consequent " << consequent << std::endl;
// 	// std::cout << "purified using EUF " << purifyEUFEq(consequent) << std::endl; // Keep working here
// 	euf_solver.add(consequent);
// 	oct_solver.add(consequent);
// 	euf_consequents.push_back(consequent);
// #if _DEBUGEXTPURIFIER_
// 	std::cout << consequent << " added to euf" << std::endl;
// #endif       
// 	return;
//       }
//       }
//     }
//       // case Z3_OP_PR_REFLEXIVITY:
//       // case Z3_OP_PR_SYMMETRY:
//     case Z3_OP_PR_ASSERTED:
//     case Z3_OP_PR_HYPOTHESIS:
//     case Z3_OP_PR_TRANSITIVITY:
//     case Z3_OP_PR_TRANSITIVITY_STAR:
//     case Z3_OP_PR_UNIT_RESOLUTION:
//     case Z3_OP_PR_MODUS_PONENS:
//     case Z3_OP_PR_TH_LEMMA:
//     case Z3_OP_PR_REWRITE:
//     case Z3_OP_PR_REWRITE_STAR:{
//       auto consequent = proof.arg(num - 1).simplify();
//       auto consequent_kind = consequent.decl().decl_kind();
//       // Avoid visited consequents and anything but equalities
//       if(earlyExit(consequent_visited, consequent) || consequent_kind != Z3_OP_EQ)
// 	return;
//       // Avoid 'high-order equalities'
//       // between {==, !=, <, >, <=, >=}
//       switch(consequent.arg(0).decl().decl_kind()){
//       case Z3_OP_EQ:
//       case Z3_OP_DISTINCT:
//       case Z3_OP_LE:
//       case Z3_OP_GE:
//       case Z3_OP_LT:
//       case Z3_OP_GT:
// 	return;
//       default:	
// 	if(isProvable(oct_solver, consequent)){
// 	  euf_solver.add(consequent);
// 	  oct_solver.add(consequent);
// 	  oct_consequents.push_back(consequent);
// #if _DEBUGEXTPURIFIER_
// 	  std::cout << consequent << " added to oct" << std::endl;
// #endif
// 	}
// 	else if(isProvable(euf_solver, consequent)){
// 	  euf_solver.add(consequent);
// 	  oct_solver.add(consequent);
// 	  euf_consequents.push_back(consequent);
// #if _DEBUGEXTPURIFIER_
// 	  std::cout << consequent << " added to euf" << std::endl;
// #endif
// 	}
// 	else
// 	  throw "Error in traverseProof::'rest'. Is the proof wrong? Perhaps my algorithm isn't complete.";
// 	return;
//       }
//     }
      
//     default:
//       return;
//     }
//   }  
//   throw "Wrong proof-term";
// }

void ThCombInterpolator::getInterpolant(){
  // Traverse Proof of QF_UFLIA
}

std::ostream & operator << (std::ostream & os, ThCombInterpolator & p){
  os << "Returns interpolant";
  return os;
}
