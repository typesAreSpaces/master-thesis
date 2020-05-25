#include "Rename.h"

void traversePartA(z3::expr const & e,
    std::vector<bool> & visited,
    std::set<std::string> & a_local_names){
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
        traversePartA(e.arg(0), visited, a_local_names);
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
        traversePartA(e.arg(0), visited, a_local_names);
        traversePartA(e.arg(1), visited, a_local_names);
        return;
      default:
        for (unsigned i = 0; i < num; i++)
          traversePartA(e.arg(i), visited, a_local_names);
        a_local_names.insert(e.decl().name().str());
        return;
    }
  }
  throw "Problem @ traversePartA: The formula e is not an expression.";
}

void traversePartB(z3::expr const & e,
    std::vector<bool> & visited,
    std::set<std::string> & a_local_names,
    std::set<std::string> & common_names){
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
        traversePartB(e.arg(0), visited, a_local_names, common_names);
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
        traversePartB(e.arg(0), visited, a_local_names, common_names);
        traversePartB(e.arg(1), visited, a_local_names, common_names);
        return;
      default:
        for (unsigned i = 0; i < num; i++)
          traversePartB(e.arg(i), visited, a_local_names, common_names);
        auto name = e.decl().name().str();
        if(a_local_names.find(name) != a_local_names.end())
          common_names.insert(name);
        return;
    }
  }
  throw "Problem @ traversePartA: The formula e is not an expression.";
}

z3::expr reformulate(z3::expr const & e,
    const std::set<std::string> & a_local_names,
    const std::set<std::string> & common_names){
  if(e.is_app()){
    unsigned num = e.num_args();
    auto f = e.decl();
    z3::expr_vector new_args(e.ctx());
    z3::sort_vector domain_sorts(e.ctx());
    for(unsigned i = 0; i < num; i++){
      new_args.push_back(reformulate(e.arg(i), a_local_names, common_names));
      domain_sorts.push_back(f.domain(i));
    }
    auto name = f.name().str();
    switch(f.decl_kind()){
      case Z3_OP_ANUM:
        return e;
      case Z3_OP_UMINUS:
        return f(reformulate(e.arg(0), a_local_names, common_names));
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
        return f(reformulate(e.arg(0), a_local_names, common_names),
            reformulate(e.arg(1), a_local_names, common_names));
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

z3::expr reformulate(z3::expr const & e, std::set<std::string> const & uncommon_names){
  if(e.is_app()){
    unsigned num = e.num_args();
    auto f = e.decl();
    z3::expr_vector new_args(e.ctx());
    z3::sort_vector domain_sorts(e.ctx());
    for(unsigned i = 0; i < num; i++){
      new_args.push_back(reformulate(e.arg(i), uncommon_names));
      domain_sorts.push_back(f.domain(i));
    }
    auto name = f.name().str();
    switch(f.decl_kind()){
      case Z3_OP_ANUM:
        return e;
      case Z3_OP_UMINUS:
        return f(reformulate(e.arg(0), uncommon_names));
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
        return f(reformulate(e.arg(0), uncommon_names),
            reformulate(e.arg(1), uncommon_names));
      default:{
                if(uncommon_names.find(name) != uncommon_names.end()){
                  // It is a common symbol
                  auto new_f = z3::function(("a_" + name).c_str(), domain_sorts, f.range());
                  return new_f(new_args);
                }
                else{
                  // It is a b local symbol
                  auto new_f = z3::function(("c_" + name).c_str(), domain_sorts, f.range());
                  return new_f(new_args);
                } 
              }
    }
  }
  throw "Problem @ reformulate: The formula e is not an expression.";
}

std::pair<z3::expr, z3::expr> rename(z3::expr & a, z3::expr & b){
  std::vector<bool> visited;
  std::set<std::string> a_local_names;
  std::set<std::string> common_names;

  traversePartA(a, visited, a_local_names);
  traversePartB(b, visited, a_local_names, common_names);

  return std::make_pair(reformulate(a, a_local_names, common_names),
      reformulate(b, a_local_names, common_names));
}

z3::expr rename(z3::expr & a, const std::set<std::string> & uncommon_names){
  return reformulate(a, uncommon_names);
}
