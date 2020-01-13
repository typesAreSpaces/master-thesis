#include "ExtPurifier.h"

ExtPurifier::ExtPurifier(z3::expr & e) :
  Purifier(e),
  euf_solver(e.ctx(), "QF_UF"), oct_solver(e.ctx(), "QF_LIA"),
  combined_solver(e.ctx(), "QF_UFLIA"),
  euf_consequents(e.ctx()), oct_consequents(e.ctx())
{
  // Notes: A QF_UF solver might not be able to produce models
  // if it has interpreted terms (i.e. terms with sort int in this case)
  // Since we don't need the models, we will only deal with unknown and
  // unsats answers from solver.check()
  unsigned num = this->euf_component.size();
  for(unsigned i = 0; i < num; i++)
    euf_solver.add(euf_component[i]);

  num = this->oct_component.size();
  for(unsigned i = 0; i < num; i++)
    oct_solver.add(oct_component[i]);
}

ExtPurifier::~ExtPurifier(){
}

bool ExtPurifier::isProvable(z3::solver & s, z3::expr const & e){
  s.push();
  s.add(!e);
  bool answer = s.check() == z3::unsat;
  s.pop();
  return answer;
}

void ExtPurifier::addConjunction(z3::expr const & e){
    if (e.is_app()) {
      z3::func_decl e_decl = e.decl();
      switch(e_decl.decl_kind()){
      case Z3_OP_AND:{
	addConjunction(e.arg(0));
	addConjunction(e.arg(1));
	return;
      }
      default:
	this->combined_solver.add(e);
	return;
      }
  }
  throw "Wrong term";
}

bool ExtPurifier::earlyExit(std::vector<bool> & visited, z3::expr const & e){
  if (visited.size() <= e.id()) {
    visited.resize(e.id()+1, false);
  }
  if (visited[e.id()]) {
    return true;
  }
  visited[e.id()] = true;
  return false;
}

// FIX: We need to do something more useful with this function
// Currently, all it does it printing stuff
void ExtPurifier::extractHypothesisFromProof(z3::expr const & proof){
  if (proof.is_app()) {
    unsigned num = proof.num_args();   
    for (unsigned i = 0; i < num; i++) 
      extractHypothesisFromProof(proof.arg(i));
    
    z3::func_decl proof_decl = proof.decl();
    switch(proof_decl.decl_kind()){
    case Z3_OP_PR_TH_LEMMA:
#if _DEBUGEXTPURIFIER_
      std::cout << proof_decl.name() << std::endl;
#endif
      return;
      
    case Z3_OP_PR_HYPOTHESIS:
    case Z3_OP_PR_ASSERTED:
#if _DEBUGEXTPURIFIER_
      std::cout << proof_decl.name() << " " << proof.arg(0) << std::endl;
#endif
      return;
      
    default:
      return;
    }
  }
  throw "Wrong proof-term";
}

void ExtPurifier::collectEqualitiesFromProof(z3::expr const & proof) {
  if(earlyExit(this->visited, proof))
    return;
    
  if (proof.is_app()) {
    unsigned num = proof.num_args();
    for (unsigned i = 0; i < num; i++) 
      collectEqualitiesFromProof(proof.arg(i));
    
    z3::func_decl proof_decl = proof.decl();
    switch(proof_decl.decl_kind()) {
    case Z3_OP_PR_MONOTONICITY:{
      auto consequent = proof.arg(num - 1).simplify();
      auto consequent_kind = consequent.decl().decl_kind();
      // Avoid visited consequents and anything but equalities
      if(earlyExit(this->consequent_visited, consequent) || consequent_kind != Z3_OP_EQ)
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
      default:	
	this->euf_solver.add(consequent);
	this->euf_consequents.push_back(consequent);
	return;
      }
    }
      // case Z3_OP_PR_REFLEXIVITY:
      // case Z3_OP_PR_SYMMETRY:
    case Z3_OP_PR_ASSERTED:
    case Z3_OP_PR_HYPOTHESIS:
    case Z3_OP_PR_TRANSITIVITY:
    case Z3_OP_PR_TRANSITIVITY_STAR:
    case Z3_OP_PR_UNIT_RESOLUTION:
    case Z3_OP_PR_MODUS_PONENS:
    case Z3_OP_PR_TH_LEMMA:
    case Z3_OP_PR_REWRITE:
    case Z3_OP_PR_REWRITE_STAR:{
      auto consequent = proof.arg(num - 1).simplify();
      auto consequent_kind = consequent.decl().decl_kind();
      // Avoid visited consequents and anything but equalities
      if(earlyExit(this->consequent_visited, consequent) || consequent_kind != Z3_OP_EQ)
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
      default:	
	// // We only collect equalities between variables
	// if(consequent.arg(0).num_args() != 0 || consequent.arg(1).num_args() != 0)
	//   return;
	// #if _DEBUGEXTPURIFIER_
	// std::cout << "Consequent " << consequent.arg(0) << " = " << consequent.arg(1) << std::endl;
	// std::cout << "Reason " << proof_decl.name() << std::endl;
	// #endif
	// auto num_subproofs = num - 1;
	// for(unsigned i = 0; i < num_subproofs; i++)
	//   extractHypothesisFromProof(proof.arg(i));
	

	// FIX: We need to separate the consequents produced
	// into their correspondant logic using the extractHypothesisFromProof
	// function, somehow

	if(isProvable(oct_solver, consequent)){
	  this->oct_solver.add(consequent);
	  this->oct_consequents.push_back(consequent);
#if _DEBUGEXTPURIFIER_
	  std::cout << consequent << " added to euf" << std::endl;
#endif
	}
	else if(isProvable(euf_solver, consequent)){
	  this->euf_solver.add(consequent);
	  this->euf_consequents.push_back(consequent);
#if _DEBUGEXTPURIFIER_
	  std::cout << consequent << " added to oct" << std::endl;
#endif
	}
	else{
#if _DEBUGEXTPURIFIER_
	  std::cout << "hmm " << consequent << std::endl;
#endif
	}
	return;
      }
    }
      
    default:
      return;
    }
  }  
  throw "Wrong proof-term";
}

void ExtPurifier::test(){
  addConjunction(this->formula);

  switch(combined_solver.check()){
  case z3::sat:
    std::cout << "Sat" << std::endl;
    break; 
  case z3::unsat:{
    std::cout << "Unsat" << std::endl;
    collectEqualitiesFromProof(combined_solver.proof());

#if _DEBUGEXTPURIFIER_
    std::cout << "Equalities collected" <<  std::endl;
    std::cout << "EUF equalities" << std::endl;
    auto num = this->euf_consequents.size();
    for(unsigned i = 0; i < num; i++){
      std::cout << i << ". " << this->euf_consequents[i].arg(0) << " = " << this->euf_consequents[i].arg(1) << std::endl;
    }

    std::cout << "OCT equalities" << std::endl;
    num = this->oct_consequents.size();
    for(unsigned i = 0; i < num; i++){
      std::cout << i << ". " << this->oct_consequents[i].arg(0) << " = " << this->oct_consequents[i].arg(1) << std::endl;
    }

    std::cout << (euf_solver.check() == z3::unsat) << std::endl;
    std::cout << (oct_solver.check() == z3::unsat) << std::endl;
#endif
    break;
  }
  case z3::unknown:
    std::cout << "Unknown" << std::endl;
    break; 
  }
}

std::ostream & operator << (std::ostream & os, ExtPurifier & p){
  os << "Implement this";
  return os;
}
