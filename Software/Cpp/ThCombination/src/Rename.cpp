#include "Rename.h"

Rename::Rename(z3::expr const & a, z3::expr const & b) :
  part_a(a), part_b(b){
  traversePartA(part_a);
  traversePartB(part_b);
  
  std::cout << "a local names" << std::endl;
  for(auto x : a_local_names)
    std::cout << x << std::endl;
  std::cout << "common names" << std::endl;
  for(auto x : common_names)
    std::cout << x << std::endl;
}

Rename::~Rename(){
}

void Rename::traversePartA(z3::expr const & e){
  if(visited.size() <= e.id())
    visited.resize(e.id()+1, false);
  if(visited[e.id()])
    return;
  
  if(e.is_app()){
    unsigned num = e.num_args();
    for (unsigned i = 0; i < num; i++)
      traversePartA(e.arg(i));
    a_local_names.insert(e.decl().name().str());
    return;
  }
  throw "Problem @ traversePartA: The formula e is not an expression.";
}

void Rename::traversePartB(z3::expr const & e){
  if(visited.size() <= e.id())
    visited.resize(e.id()+1, false);
  if(visited[e.id()])
    return;
  
  if(e.is_app()){
    unsigned num = e.num_args();
    for (unsigned i = 0; i < num; i++)
      traversePartB(e.arg(i));
    auto name = e.decl().name().str();
    if(a_local_names.find(name) != a_local_names.end())
      common_names.insert(name);
    return;
  }
  throw "Problem @ traversePartA: The formula e is not an expression.";
}

z3::expr Rename::reformulate(z3::expr const & e){
  if(e.is_app()){
    unsigned num = e.num_args();
    auto f = e.decl();
    
    if(num == 0){
      // Missing!
    }
    else{
      z3::expr_vector args(e.ctx());
      for(unsigned i = 0; i < num; i++){
	args.push_back(reformulate(e.arg(i)));
      }
      auto name = f.name().str();
      if(common_names.find(name) == common_names.end()){
	// It is a common symbol
	auto new_f = z3::function(z3::symbol("hah"), num, , f.range());
      }
      else if(a_local_names.find(name) == a_local_names.end()){
	// It is an a local symbol
      }
      else{
	// It is a b local symbol
      }
    }
    
    return;
  }
  throw "Problem @ reformulate: The formula e is not an expression.";
}
