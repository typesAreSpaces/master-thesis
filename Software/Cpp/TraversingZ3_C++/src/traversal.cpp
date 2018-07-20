#include "traversal.h"

void visit(z3::expr const & e) {
  if (e.is_app()) {
    unsigned num = e.num_args();
    for (unsigned i = 0; i < num; i++)
      visit(e.arg(i));
    // do something
    // Example: print the visited expression
    z3::func_decl f = e.decl();
    std::cout << "Application of " << f.name() << ": " << e << "\nHash: " << e.hash() << " Arity: " << e.num_args() <<"\n";
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
      z3::func_decl f = temp.decl();
      std::cout << "Application of " << f.name() << ": " << temp << "\nHash: " << temp.hash() << " Arity: " << temp.num_args() <<"\n";
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

void insert(z3::expr const & e, std::stack<z3::expr> & s, std::map<unsigned, int> & gas){
  int _na = e.num_args();
  if(_na == 0){
    s.push(e);
    gas.insert(std::make_pair(e.hash(), e.num_args()));
  }
  else if(_na == 1){
    s.push(e), s.push(e.arg(0));
    gas.insert(std::make_pair(e.hash(), e.num_args()));
    gas.insert(std::make_pair(e.arg(0).hash(), e.arg(0).num_args()));
  }
  else{
    for(int i = _na - 1; i > 0; --i){
      s.push(e.arg(i));
      gas.insert(std::make_pair(e.arg(i).hash(), e.arg(i).num_args()));
    }
    s.push(e), s.push(e.arg(0));
    gas.insert(std::make_pair(e.hash(), e.num_args()));
    gas.insert(std::make_pair(e.arg(0).hash(), e.arg(0).num_args()));
  }
}
void move(std::stack<z3::expr> & s){
  z3::expr _e = s.top();
  s.pop();
  z3::expr _e2 = s.top();
  s.pop();
  s.push(_e), s.push(_e2);
}

void visitPostOrderWithStack(z3::expr const & e){
  std::stack<z3::expr> s;
  std::map<unsigned, int> gas;
  
  insert(e, s, gas);
  while(!s.empty()){  
    z3::expr _e = s.top();
    s.pop();
    if(gas[_e.hash()] == 0){
      // do something
      if(_e.is_app()){
	// do something
	z3::func_decl f = _e.decl();
	std::cout << "Application of " << f.name() << ": " << _e << "\nHash: " << _e.hash() << " Arity: " << _e.num_args() << "\n";
      }
      else if (_e.is_quantifier()){
	// do something
      }
      else{
	// do something
      }
      if(!s.empty()){
	_e = s.top();
	gas[_e.hash()] -= 1;
	if(gas[_e.hash()] > 0)
	  move(s);
      }
    }
    else
      insert(_e, s, gas);
  }
}

