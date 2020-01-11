#include "Util.h"

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
  throw "Wrong e-term";
}

bool earlyExit(std::vector<bool> & visited, z3::expr const & e){
  if (visited.size() <= e.id()) {
    visited.resize(e.id()+1, false);
  }
  if (visited[e.id()]) {
    return true;
  }
  visited[e.id()] = true;
  return false;
}

void extractHypothesisFromProof(z3::expr const & proof){
  if (proof.is_app()) {
    unsigned num = proof.num_args();   
    for (unsigned i = 0; i < num; i++) 
      extractHypothesisFromProof(proof.arg(i));
    
    z3::func_decl proof_decl = proof.decl();
    switch(proof_decl.decl_kind()){
    case Z3_OP_PR_TH_LEMMA:{
      std::cout << proof_decl.name() << std::endl;
      return;
    }
    case Z3_OP_PR_HYPOTHESIS:
    case Z3_OP_PR_ASSERTED:{
      std::cout << proof_decl.name() << " " << proof.arg(0) << std::endl;
      return;
    }
      
    default:
      return;
    }
  }
  throw "Wrong proof-term";
}

void collectEqualitiesFromProof(std::vector<bool> & visited,
				std::vector<bool> & consequent_visited,
				z3::expr_vector & consequents,
				z3::expr const & proof) {
  if(earlyExit(visited, proof))
    return;
    
  if (proof.is_app()) {
    unsigned num = proof.num_args();
    for (unsigned i = 0; i < num; i++) 
      collectEqualitiesFromProof(visited, consequent_visited, consequents, proof.arg(i));
    
    z3::func_decl proof_decl = proof.decl();
    switch(proof_decl.decl_kind()) {
      // case Z3_OP_PR_REFLEXIVITY:
      // case Z3_OP_PR_SYMMETRY:
    case Z3_OP_PR_HYPOTHESIS:
    case Z3_OP_PR_TRANSITIVITY:
    case Z3_OP_PR_TRANSITIVITY_STAR:
    case Z3_OP_PR_MONOTONICITY:
    case Z3_OP_PR_UNIT_RESOLUTION:
    case Z3_OP_PR_MODUS_PONENS:
    case Z3_OP_PR_TH_LEMMA:
    case Z3_OP_PR_REWRITE:
    case Z3_OP_PR_REWRITE_STAR:{
      auto consequent = proof.arg(num - 1).simplify();
      auto consequent_kind = consequent.decl().decl_kind();
      // Avoid visited consequents and anything but equalities
      if(earlyExit(consequent_visited, consequent) || consequent_kind != Z3_OP_EQ)
	return;
      // Avoid 'high-order equalities'
      // between {==, !=, <, >, <=, >=}
      switch(consequent.arg(0).decl().decl_kind()){
      case Z3_OP_EQ:
      case Z3_OP_DISTINCT:
      case Z3_OP_LE:
      case Z3_OP_GE:
      case Z3_OP_LT:
      case Z3_OP_GT:
	return;
      default:{
	
	std::cout << std::endl;
	std::cout << "Consequent " << consequent.arg(0) << " = " << consequent.arg(1) << std::endl;
	std::cout << "Reason " << proof_decl.name() << std::endl;
	
	auto num_subproofs = num - 1;
	for(unsigned i = 0; i < num_subproofs; i++)
	  extractHypothesisFromProof(proof.arg(i));
	
	consequents.push_back(consequent);
	// std::cout << proof_decl.name() << " " << consequent
	// 		<< " " << consequent.id() << std::endl;
	return;
      }
      }
    }
      
    default:
      return;
    }
  }  
  throw "Wrong proof-term";
}
