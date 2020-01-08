#include "Purifier.h"
#include <vector>

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

int main(){
  
  z3::set_param("proof", "true");
  z3::context c;
  c.set(":pp-min-alias-size", 1000000);
  c.set(":pp-max-depth", 1000000);
  
  z3::sort _s = c.int_sort();
  z3::expr x1 = c.constant("x1", _s);
  z3::expr x2 = c.constant("x2", _s);
  z3::expr x3 = c.constant("x3", _s);
  
  // z3::func_decl f = c.function("f", _s, _s);
  // z3::expr formula = f(f(x1) - f(x2)) != f(x3) && x1 <= x2 && (x2 + x3) <= x1 && 0 <= x3 && f(x1) <= f(x2);
  // z3::expr formula = f(f(x1) - f(x2)) != f(x3) && x1 <= x2 && (x2 + x3) <= x1 && 0 <= x3;
  // z3::expr formula = x1 <= f(x1);
  // z3::expr formula = (x2 >= x1) && ((x1 - x3) >= x2) && (x3 >= 0)
  //    && (f(f(x1) - f(x2)) != f(x3));

  // z3::func_decl g = c.function("g", _s, _s);
  // z3::expr formula = g(f(x1 - 2)) == x1 + 2 && g(f(x2)) == x2 - 2 && (x2 + 1 == x1 - 1);
  
  z3::func_decl f = c.function("f", _s, _s, _s);
  z3::expr formula =
    f(x1, 0) >= x3
    && f(x2, 0) <= x3
    && x1 >= x2
    && x2 >= x1
    && (x3 - f(x1, 0) >= 1);
  
  // std::cout << "Original input formula:" << std::endl;
  // std::cout << formula << std::endl;

  Purifier p = Purifier(formula);
  std::cout << formula << std::endl;

  std::cout << p << std::endl;

  // z3::solver s(c);
  // addConjunction(s, formula);

  // switch(s.check()){
  // case z3::sat:
  //   std::cout << "Sat" << std::endl;
  //   break; 
  // case z3::unsat:{
  //   std::cout << "Unsat" << std::endl;
    
  //   // std::cout << "Unsat proof" << std::endl;
  //   // std::cout << s.proof() << std::endl;
    
  //   std::vector<bool> visited;
  //   std::vector<bool> consequent_visited;
  //   z3::expr_vector consequents(c);
  //   collectEqualitiesFromProof(visited, consequent_visited, consequents, s.proof());

  //   std::cout << std::endl;
  //   std::cout << "Terms collected:" <<  std::endl;
  //   auto num = consequents.size();
  //   for(unsigned i = 0; i < num; i++)
  //     std::cout << i << ". " << consequents[i].arg(0) << " = " << consequents[i].arg(1) << std::endl;
    
  //   break;
  // }
  // case z3::unknown:
  //   std::cout << "Unknown" << std::endl;
  //   break; 
  // }
    
  return 0;
}
