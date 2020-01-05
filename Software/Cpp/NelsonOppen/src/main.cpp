#include "Purifier.h"
#include <vector>

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
    
    z3::func_decl f = proof.decl();
    switch(f.decl_kind()){
    case Z3_OP_PR_HYPOTHESIS:{
      std::cout << "Hypothesis" << f.name() << " " << proof << std::endl;
      break;
    }
      
    default:
      break;
    }
  }
  else if (proof.is_quantifier())
    extractHypothesisFromProof(proof.body());
  else 
    assert(proof.is_var());
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
    
    z3::func_decl f = proof.decl();
    switch(f.decl_kind()){
      // case Z3_OP_PR_REFLEXIVITY:
      // case Z3_OP_PR_SYMMETRY:
    case Z3_OP_PR_TRANSITIVITY:
    case Z3_OP_PR_TRANSITIVITY_STAR:
    case Z3_OP_PR_MONOTONICITY:
    case Z3_OP_PR_UNIT_RESOLUTION:
    case Z3_OP_PR_MODUS_PONENS:
    case Z3_OP_PR_TH_LEMMA:
    case Z3_OP_PR_REWRITE:
    case Z3_OP_PR_REWRITE_STAR:{

      auto consequent = proof.arg(num - 1).simplify();
      if(earlyExit(consequent_visited, consequent))
	return;
      // Check if the consequent isn't trivial
      if(consequent.decl().decl_kind() == Z3_OP_TRUE)
	break;
      // Avoid anything but equalities
      if(consequent.decl().decl_kind() != Z3_OP_EQ)
	break;
      // Avoid relations between {equalities, dis-equalities, <, >, <=, >=}
      if(consequent.num_args() > 0
	 && consequent.decl().decl_kind() == Z3_OP_EQ
	 && (consequent.arg(0).decl().decl_kind() == Z3_OP_EQ
	     || consequent.arg(0).decl().decl_kind() == Z3_OP_DISTINCT
	     || consequent.arg(0).decl().decl_kind() == Z3_OP_LE
	     || consequent.arg(0).decl().decl_kind() == Z3_OP_GE
	     || consequent.arg(0).decl().decl_kind() == Z3_OP_LT
	     || consequent.arg(0).decl().decl_kind() == Z3_OP_GT))
      	break;

      auto num_args_consequent = consequent.num_args() - 1;
      for(unsigned i = 0; i < num_args_consequent; i++)
	extractHypothesisFromProof(consequent.arg(i));
	
      
      consequents.push_back(consequent);
      // std::cout << f.name() << " " << consequent
      // 		<< " " << consequent.id() << std::endl;
    }
      
    default:
      break;
    }
  }
  else if (proof.is_quantifier()) 
    collectEqualitiesFromProof(visited, consequent_visited, consequents, proof.body());
  else
    assert(proof.is_var());
}

int main(){
  
  z3::set_param("proof", "true");
  z3::context c;
  c.set(":pp-min-alias-size", 1000000);
  c.set(":pp-max-depth", 1000000);
  
  z3::sort Q = c.real_sort();
  z3::expr x1 = c.constant("x1", Q);
  z3::expr x2 = c.constant("x2", Q);
  z3::expr x3 = c.constant("x3", Q);
  
  z3::func_decl f = c.function("f", Q, Q);
  z3::expr formula = f(f(x1) - f(x2)) != f(x3) && x1 <= x2 && (x2 + x3) <= x1 && 0 <= x3 && f(x1) <= f(x2);
  // z3::expr formula = f(f(x1) - f(x2)) != f(x3) && x1 <= x2 && (x2 + x3) <= x1 && 0 <= x3;
  // z3::expr formula = x1 <= f(x1);
  // z3::expr formula = (x2 >= x1) && ((x1 - x3) >= x2) && (x3 >= 0)
  //    && (f(f(x1) - f(x2)) != f(x3));

  // z3::func_decl g = c.function("g", Q, Q);
  // z3::expr formula = g(f(x1 - 2)) == x1 + 2 && g(f(x2)) == x2 - 2 && (x2 + 1 == x1 - 1);
  
  // z3::func_decl f = c.function("f", Q, Q, Q);
  // z3::expr formula =
  //   f(x1, 0) >= x3
  //   && f(x2, 0) <= x3
  //   && x1 >= x2
  //   && x2 >= x1
  //   && (x3 - f(x1, 0) >= 1);
  
  std::cout << "Original input formula:" << std::endl;
  std::cout << formula << std::endl;

  // Purifier p = Purifier(formula);

  z3::solver s(c);
  s.add(formula);

  switch(s.check()){
  case z3::sat:
    std::cout << "Sat" << std::endl;
    break; 
  case z3::unsat:{
    std::cout << "Unsat" << std::endl;
    
    std::cout << "Unsat proof" << std::endl;
    std::cout << s.proof() << std::endl;
    
    std::vector<bool> visited;
    std::vector<bool> consequent_visited;
    z3::expr_vector consequents(c);
    collectEqualitiesFromProof(visited, consequent_visited, consequents, s.proof());
    std::cout << "Terms collected:" <<  std::endl;
    auto num = consequents.size();
    for(unsigned i = 0; i < num; i++)
      std::cout << i << ". " << consequents[i] << std::endl;
    
    break;
  }
  case z3::unknown:
    std::cout << "Unknown" << std::endl;
    break; 
  }
    
  return 0;
}
