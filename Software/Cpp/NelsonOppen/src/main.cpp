#include "Purifier.h"
#include <vector>

void collectEqualitiesFromProof(std::vector<bool> & visited, z3::expr const & e) {
  if (visited.size() <= e.id()) {
    visited.resize(e.id()+1, false);
  }
  if (visited[e.id()]) {
    return;
  }
  visited[e.id()] = true;
    
  if (e.is_app()) {
    unsigned num = e.num_args();
    
    for (unsigned i = 0; i < num; i++) {
      collectEqualitiesFromProof(visited, e.arg(i));
    }

    // do something
    // Example: print the visited expression
    
    z3::func_decl f = e.decl();
    switch(f.decl_kind()){
    case Z3_OP_PR_REFLEXIVITY:
    case Z3_OP_PR_SYMMETRY:
    case Z3_OP_PR_TRANSITIVITY:
    case Z3_OP_PR_TRANSITIVITY_STAR:
    case Z3_OP_PR_MONOTONICITY:{

      auto conclusion = e.arg(num - 1).simplify();
      // Check if the conclusion isn't trivial
      if(conclusion.decl().decl_kind() == Z3_OP_TRUE)
	break;
      // Avoid relations between equalities
      if(conclusion.num_args() > 0
	 && conclusion.decl().decl_kind() == Z3_OP_EQ
	 && (conclusion.arg(0).decl().decl_kind() == Z3_OP_EQ))
      	break;
      // Avoid anything but equalities
      if(conclusion.decl().decl_kind() != Z3_OP_EQ)
	break;
      std::cout << f.name() << " " << conclusion
		<< " " << conclusion.id() << std::endl << std::endl;
    }
    case Z3_OP_PR_UNIT_RESOLUTION:
    case Z3_OP_PR_MODUS_PONENS:
    case Z3_OP_PR_TH_LEMMA:
    case Z3_OP_PR_REWRITE:
    case Z3_OP_PR_REWRITE_STAR:{
      auto conclusion = e.arg(num - 1).simplify();
      // Check if the conclusion isn't trivial
      if(conclusion.decl().decl_kind() == Z3_OP_TRUE)
	break;
      // Avoid relations between equalities
      if(conclusion.num_args() > 0
	 && conclusion.decl().decl_kind() == Z3_OP_EQ
	 && (conclusion.arg(0).decl().decl_kind() == Z3_OP_EQ))
      	break;
      // Avoid anything but equalities
      if(conclusion.decl().decl_kind() != Z3_OP_EQ)
	break;
      std::cout << f.name() << " " << conclusion
		<< " " << conclusion.id() << std::endl << std::endl;
      break;
    }
    default:
      break;
    }
  }
  else if (e.is_quantifier()) {
    collectEqualitiesFromProof(visited, e.body());
    // do something
  }
  else { 
    assert(e.is_var());
    // do something
  }
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

  //  Purifier p = Purifier(formula);
  // std::cout << p << std::endl;

  z3::solver s(c);
  s.add(formula);

  switch(s.check()){
  case z3::sat:
    std::cout << "Sat" << std::endl;
    break; 
  case z3::unsat:{
    std::cout << "Unsat" << std::endl << std::endl;
    // std::cout << s.proof() << std::endl;
    std::cout << "Traversing the proof:" << std::endl;
    std::vector<bool> visited;
    collectEqualitiesFromProof(visited, s.proof());
    
    break;
  }
  case z3::unknown:
    std::cout << "Unknown" << std::endl;
    break; 
  }
    
  return 0;
}
