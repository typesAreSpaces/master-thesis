#include "Rename.h"

Rename::Rename(z3::expr const & a, z3::expr const & b) :
  part_a(a), part_b(b){
  traversePartA(part_a);
  traversePartB(part_b);

  // Debugging ---------------------------------
  std::cout << "Part a" << std::endl;
  std::cout << part_a << std::endl;
  std::cout << "Part b" << std::endl;
  std::cout << part_b << std::endl;
  std::cout << "a local names" << std::endl;
  for(auto x : a_local_names)
    std::cout << x << std::endl;
  std::cout << "common names" << std::endl;
  for(auto x : common_names)
    std::cout << x << std::endl;
  std::cout << "New Part a" << std::endl;
  std::cout << reformulate(part_a) << std::endl;
  std::cout << "New Part b" << std::endl;
  std::cout << reformulate(part_b) << std::endl;
  //           ---------------------------------
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
    auto f = e.decl();
    switch(f.decl_kind()){
    case Z3_OP_ANUM:
      return;
    case Z3_OP_UMINUS:
      traversePartA(e.arg(0));
      return;
    case Z3_OP_AND:
    case Z3_OP_EQ:
    case Z3_OP_DISTINCT:
    case Z3_OP_LE:
    case Z3_OP_GE:
    case Z3_OP_LT:
    case Z3_OP_GT:
    case Z3_OP_ADD:
    case Z3_OP_SUB:
    case Z3_OP_MUL:
    case Z3_OP_DIV:
    case Z3_OP_IDIV:
      traversePartA(e.arg(0));
      traversePartA(e.arg(1));
      return;
    default:
      for (unsigned i = 0; i < num; i++)
	traversePartA(e.arg(i));
      a_local_names.insert(e.decl().name().str());
      return;
    }
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
    auto f = e.decl();
    switch(f.decl_kind()){
    case Z3_OP_ANUM:
      return;
    case Z3_OP_UMINUS:
      traversePartB(e.arg(0));
      return;
    case Z3_OP_AND:
    case Z3_OP_EQ:
    case Z3_OP_DISTINCT:
    case Z3_OP_LE:
    case Z3_OP_GE:
    case Z3_OP_LT:
    case Z3_OP_GT:
    case Z3_OP_ADD:
    case Z3_OP_SUB:
    case Z3_OP_MUL:
    case Z3_OP_DIV:
    case Z3_OP_IDIV:
      traversePartB(e.arg(0));
      traversePartB(e.arg(1));
      return;
    default:
      for (unsigned i = 0; i < num; i++)
	traversePartB(e.arg(i));
      auto name = e.decl().name().str();
      if(a_local_names.find(name) != a_local_names.end())
	common_names.insert(name);
      return;
    }
  }
  throw "Problem @ traversePartA: The formula e is not an expression.";
}

z3::expr Rename::reformulate(z3::expr const & e){
  if(e.is_app()){
    unsigned num = e.num_args();
    auto f = e.decl();
    z3::expr_vector new_args(e.ctx());
    z3::sort_vector domain_sorts(e.ctx());
    for(unsigned i = 0; i < num; i++){
      new_args.push_back(reformulate(e.arg(i)));
      domain_sorts.push_back(f.domain(i));
    }
    auto name = f.name().str();
    switch(f.decl_kind()){
    case Z3_OP_ANUM:
      return e;
    case Z3_OP_UMINUS:
      return f(reformulate(e.arg(0)));
    case Z3_OP_AND:
    case Z3_OP_EQ:
    case Z3_OP_DISTINCT:
    case Z3_OP_LE:
    case Z3_OP_GE:
    case Z3_OP_LT:
    case Z3_OP_GT:
    case Z3_OP_ADD:
    case Z3_OP_SUB:
    case Z3_OP_MUL:
    case Z3_OP_DIV:
    case Z3_OP_IDIV:
      return f(reformulate(e.arg(0)), reformulate(e.arg(1)));
    default:{
      if(common_names.find(name) != common_names.end()){
	// It is a common symbol
	auto new_f = z3::function(("c_" + name).c_str(), domain_sorts, f.range());
	return new_f(new_args);
      }
      else if(a_local_names.find(name) != a_local_names.end()){
	// It is an a local symbol
	auto new_f = z3::function(("a_" + name).c_str(), domain_sorts, f.range());
	return new_f(new_args);
      }
      else{
	// It is a b local symbol
	auto new_f = z3::function(("b_" + name).c_str(), domain_sorts, f.range());
	return new_f(new_args);
      } 
    }
    }
  }
  throw "Problem @ reformulate: The formula e is not an expression.";
}
