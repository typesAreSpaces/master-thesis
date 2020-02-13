#include "UtilsProof.h"

void addConjunction(z3::solver & s, z3::expr const & e){
    if (e.is_app()) {
      z3::func_decl e_decl = e.decl();
      switch(e_decl.decl_kind()){
      case Z3_OP_AND:{
	addConjunction(s, e.arg(0));
	addConjunction(s, e.arg(1));
	return;
      }
      default:
	s.add(e);
	return;
      }
  }
  throw "Wrong term";
}

void traverseProof1(z3::expr const & proof) {
  if(proof.is_app()){
    unsigned num = proof.num_args();

    z3::func_decl proof_decl = proof.decl();
    
    switch(proof_decl.decl_kind()){
      
    case Z3_OP_PR_ASSERTED:
    case Z3_OP_PR_LEMMA:
    case Z3_OP_PR_UNIT_RESOLUTION:
    case Z3_OP_PR_TH_LEMMA:{
      for(unsigned i = 0; i < num - 1; i++)
	traverseProof1(proof.arg(i));
      
      std::cout << proof_decl.name() << ": ";
      
      for(unsigned i = 0; i < num - 1; i++){
	unsigned temp_size = proof.arg(i).num_args();
	std::cout << proof.arg(i).arg(temp_size - 1) << ", ";
      }
      
      std::cout << " |- " << proof.arg(num - 1) << std::endl;
      
      return;
    }
    default:{
      traverseProof2(proof);
      
      // std::cout << " hmm |- " << proof.arg(num - 1) << std::endl;
      std::cout << proof_decl.name() << ": ";
      std::cout << "(mysterious step) |- " << proof.arg(num - 1) << std::endl;
      
      return;
    }
    }
  }
  throw "Wrong proof-term in traverseProof1";
}

void traverseProof2(z3::expr const & proof) {
  if(proof.is_app()){
    unsigned num = proof.num_args();

    z3::func_decl proof_decl = proof.decl();
    switch(proof_decl.decl_kind()){
      
    case Z3_OP_PR_ASSERTED:
    case Z3_OP_PR_LEMMA:
    case Z3_OP_PR_UNIT_RESOLUTION:
    case Z3_OP_PR_TH_LEMMA:{
      traverseProof1(proof);
      // std::cout << "hmm " << proof.arg(num - 1) << ", ";
      
      return;
    }
    default:{
      for(unsigned i = 0; i < num - 1; i++)
	traverseProof2(proof.arg(i));
      
      return;
    }
    }
  }
  throw "Wrong proof-term in traverseProof2";
}


  // if(earlyExit(visited, proof))
  //   return;
    
  // if (proof.is_app()) {
  //   unsigned num = proof.num_args();
  //   for (unsigned i = 0; i < num; i++) 
  //     collectEqualitiesFromProofAux(visited, consequent_visited, consequents, proof.arg(i));
    
  //   z3::func_decl proof_decl = proof.decl();
  //   switch(proof_decl.decl_kind()) {
  //     // case Z3_OP_PR_REFLEXIVITY:
  //     // case Z3_OP_PR_SYMMETRY:
  //   case Z3_OP_PR_ASSERTED:
  //   case Z3_OP_PR_HYPOTHESIS:
  //   case Z3_OP_PR_TRANSITIVITY:
  //   case Z3_OP_PR_TRANSITIVITY_STAR:
  //   case Z3_OP_PR_MONOTONICITY:
  //   case Z3_OP_PR_UNIT_RESOLUTION:
  //   case Z3_OP_PR_MODUS_PONENS:
  //   case Z3_OP_PR_TH_LEMMA:
  //   case Z3_OP_PR_REWRITE:
  //   case Z3_OP_PR_REWRITE_STAR:{
  //     auto consequent = proof.arg(num - 1).simplify();
  //     auto consequent_kind = consequent.decl().decl_kind();
  //     // Avoid visited consequents and anything but equalities
  //     if(earlyExit(consequent_visited, consequent) || consequent_kind != Z3_OP_EQ)
  // 	return;
  //     // Avoid 'high-order equalities'
  //     // between {==, !=, <, >, <=, >=}
  //     switch(consequent.arg(0).decl().decl_kind()){
  //     case Z3_OP_EQ:
  //     case Z3_OP_DISTINCT:
  //     case Z3_OP_LE:
  //     case Z3_OP_GE:
  //     case Z3_OP_LT:
  //     case Z3_OP_GT:
  // 	return;
  //     default:	
  // 	// // We only collect equalities between variables
  // 	if(consequent.arg(0).num_args() != 0 || consequent.arg(1).num_args() != 0)
  // 	  return;
	
  // 	std::cout << std::endl;
  // 	std::cout << "Consequent " << consequent.arg(0) << " = " << consequent.arg(1) << std::endl;
  // 	std::cout << "Reason " << proof_decl.name() << std::endl;
	
  // 	auto num_subproofs = num - 1;
  // 	for(unsigned i = 0; i < num_subproofs; i++)
  // 	  extractHypothesisFromProof(proof.arg(i));
	
  // 	consequents.push_back(consequent);
  // 	return;
  //     }
  //   }
      
  //   default:
  //     return;
  //   }
  // }  
  // throw "Wrong proof-term";
