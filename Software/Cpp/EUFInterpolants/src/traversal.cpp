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

void visitWithStack(z3::expr & e) {
  z3::expr & _temp = e;
  std::stack<z3::expr> s;
  s.push(e);
  while(!s.empty()){
    _temp = s.top();
    s.pop();
    if(_temp.is_app()){
      // do something
      z3::func_decl f = _temp.decl();
      std::cout << "Application of " << f.name() << ": " << _temp << "\nHash: " << _temp.hash() <<"\n";
      unsigned num = _temp.num_args();
      std::cout << num << std::endl;
      for(unsigned i = 0; i < num; ++i)
	s.push(_temp.arg(i));
    }
    else if(_temp.is_quantifier()){
      s.push(_temp.body());
      // do something
    }
    else{
      assert(e.is_var());
      // do something
    }
  }
}
