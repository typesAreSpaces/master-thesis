#include "ThCombInterpolator.h"
#define _DEBUGEXTPURIFIER_ false

ThCombInterpolator::ThCombInterpolator(z3::context & ctx,
				       z3::expr const & formula_a, z3::expr const & formula_b) :
  ctx(ctx), part_a(formula_a), part_b(formula_b),
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

void ThCombInterpolator::printf___(z3::expr const & proof){
  
  unsigned num = proof.num_args();
  z3::func_decl proof_decl = proof.decl();
  
  std::cout << proof_decl.name() << ": ";    
  for(unsigned i = 0; i < num - 1; i++){
    unsigned temp_size = proof.arg(i).num_args();
    std::cout << proof.arg(i).arg(temp_size - 1) << " ; " << proof.arg(i).arg(temp_size - 1) << ", ";
  }
  std::cout << "|- " << proof.arg(num - 1) << " ; " << proof.arg(num - 1) << std::endl;
}

void ThCombInterpolator::traverseProof1(z3::expr const & proof) {
  if(proof.is_app()){
    unsigned num = proof.num_args();
    z3::func_decl proof_decl = proof.decl();
    switch(proof_decl.decl_kind()){
    case Z3_OP_PR_LEMMA:{      
      // Printing -----
      printf___(proof);
      //          -----
      return;
    }
    case Z3_OP_PR_ASSERTED:{
      // Printing -----
      printf___(proof);
      //          -----
      return;
    }
    case Z3_OP_PR_UNIT_RESOLUTION:{
      for(unsigned i = 0; i < num - 1; i++)
	traverseProof1(proof.arg(i));
      // Printing -----
      printf___(proof);
      //          -----
      return;
    }
    case Z3_OP_PR_TH_LEMMA:{
      for(unsigned i = 0; i < num - 1; i++)
	traverseProof1(proof.arg(i));
      // Printing -----
      printf___(proof);
      //          -----
      return;
    }
    default:{
      z3::expr_vector hyps(proof.ctx());
      traverseProof2(proof, hyps);
      // Printing ------------------------------------------
      std::cout << proof_decl.name() << ": ";
      unsigned num_hyps = hyps.size();
      for(unsigned i = 0; i < num_hyps; i++)
	std::cout << hyps[i] << " ; " << hyps[i] << ", "; 
      std::cout << "|- " << proof.arg(num - 1) << " ; " << proof.arg(num - 1) << std::endl;
      //          ------------------------------------------
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
    case Z3_OP_PR_TH_LEMMA:{
      traverseProof1(proof);
      hyps.push_back(proof.arg(num - 1));
      return;
    }
    default:{      
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
  z3::solver temp_solver(p.ctx, "QF_UFLIA");
  
  p.part_a.addEufFormulasToSolver(temp_solver);
  p.part_a.addOctFormulasToSolver(temp_solver);
  p.part_b.addEufFormulasToSolver(temp_solver);
  p.part_b.addOctFormulasToSolver(temp_solver);
  
  if(temp_solver.check() == z3::unsat){
    // std::cout << temp_solver.proof() << std::endl;
    p.traverseProof1(temp_solver.proof());
  }
  
  os << "Returns interpolant";
  return os;
}
