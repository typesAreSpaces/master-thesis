#include "ThCombInterpolator.h"
#define _DEBUGEXTPURIFIER_ false

ThCombInterpolator::ThCombInterpolator(z3::expr & e) :
  Purifier(e),
  euf_solver(e.ctx(), "QF_UF"), oct_solver(e.ctx(), "QF_LIA"),
  euf_consequents(e.ctx()), oct_consequents(e.ctx())
{
  unsigned num = euf_component.size();
  for(unsigned i = 0; i < num; i++)
    euf_solver.add(euf_component[i]);

  num = oct_component.size();
  for(unsigned i = 0; i < num; i++)
    oct_solver.add(oct_component[i]);
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

bool ThCombInterpolator::earlyExit(std::vector<bool> & visited, z3::expr const & e){
  if (visited.size() <= e.id()) {
    visited.resize(e.id()+1, false);
  }
  if (visited[e.id()]) {
    return true;
  }
  visited[e.id()] = true;
  return false;
}

void ThCombInterpolator::traverseProof(z3::expr const & proof) {
  if(earlyExit(visited, proof))
    return;
    
  if (proof.is_app()) {
    unsigned num = proof.num_args();
    for (unsigned i = 0; i < num; i++) 
      traverseProof(proof.arg(i));
    
    z3::func_decl proof_decl = proof.decl();
    switch(proof_decl.decl_kind()) {
    case Z3_OP_PR_MONOTONICITY:{
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
      default:
	euf_solver.add(consequent);
	oct_solver.add(consequent);
	euf_consequents.push_back(consequent);
#if _DEBUGEXTPURIFIER_
	std::cout << consequent << " added to euf" << std::endl;
#endif       
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
      default:	
	if(isProvable(oct_solver, consequent)){
	  euf_solver.add(consequent);
	  oct_solver.add(consequent);
	  oct_consequents.push_back(consequent);
#if _DEBUGEXTPURIFIER_
	  std::cout << consequent << " added to oct" << std::endl;
#endif
	}
	else if(isProvable(euf_solver, consequent)){
	  euf_solver.add(consequent);
	  oct_solver.add(consequent);
	  euf_consequents.push_back(consequent);
#if _DEBUGEXTPURIFIER_
	  std::cout << consequent << " added to euf" << std::endl;
#endif
	}
	else
	  throw "Error in traverseProof::'rest'. Is the proof wrong? Perhaps my algorithm isn't complete.";
	return;
      }
    }
      
    default:
      return;
    }
  }  
  throw "Wrong proof-term";
}

void ThCombInterpolator::collectEqualities(){
  z3::solver combined_solver(formula.ctx(), "QF_UFLIA");
  addConjunction(combined_solver, formula);
  
  switch(combined_solver.check()){
  case z3::sat:
    std::cout << "Sat" << std::endl;
    return;
  case z3::unsat:{
    std::cout << "Unsat" << std::endl;
    traverseProof(combined_solver.proof());
    return;
  }
  case z3::unknown:
    std::cout << "Unknown" << std::endl;
    return;
  }
}

std::ostream & operator << (std::ostream & os, ThCombInterpolator & p){
    os << "Equalities collected" <<  std::endl;
    
    os << "EUF equalities" << std::endl;
    unsigned num = p.euf_consequents.size();
    for(unsigned i = 0; i < num; i++)
      os << i << ". " << p.euf_consequents[i].arg(0) << " = " << p.euf_consequents[i].arg(1) << std::endl;

    os << "OCT equalities" << std::endl;
    num = p.oct_consequents.size();
    for(unsigned i = 0; i < num; i++)
      //      os << i << ". " << p.oct_consequents[i].arg(0) << " = " << p.oct_consequents[i].arg(1) << std::endl;
      os << i << ". " << p.oct_consequents[i] << std::endl;

    auto euf_ans = p.euf_solver.check();
    auto oct_ans = p.oct_solver.check();

    if(euf_ans != z3::unsat && oct_ans != z3::unsat)
      os << "Neither of the solvers reached a contradiction";
    else{    
      if(p.euf_solver.check() == z3::unsat)
	os << "The QF_UF solver reached a contradiction" << std::endl;
      if (p.oct_solver.check() == z3::unsat)
	os << "The QF_LIA solver reached a contradiction" << std::endl;
    }
    
  return os;
}
