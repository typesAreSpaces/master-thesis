#include "traversal.h"

void visit(z3::expr const & e) {
  if (e.is_app()) {
    unsigned num = e.num_args();
    for (unsigned i = 0; i < num; i++) {
      visit(e.arg(i));
    }
    // do something
    // Example: print the visited expression
    z3::func_decl f = e.decl();
    std::cout << "Application of " << f.name() << ": " << e << "\nHash: " << e.hash() <<"\n";
  }
  else if (e.is_quantifier()) {
    visit(e.body());
    // do something
  }
  else { 
    assert(e.is_var());
    // do something
  }
}

void visitWithStack(z3::expr const & e){
  std::stack<z3::expr> s;
  s.push(e);
  while(!s.empty()){
    z3::expr temp = s.top();
    s.pop();
    if(temp.is_app()){
      unsigned num = temp.num_args();
      for(unsigned i = 0; i < num; ++i)
	s.push(temp.arg(i));
      // do something
      // Example: print the visited expression
      z3::func_decl f = e.decl();
      std::cout << "Application of " << f.name() << ": " << temp << "\nHash: " << temp.hash() <<"\n";
    }
    else if (temp.is_quantifier()){
      s.push(temp.body());
      // do something
    }
    else{
      assert(temp.is_var());
      // do something
    }
  }
}

