#include "Purifier.h"

unsigned Purifier::fresh_var_id = 0;

Purifier::Purifier(z3::expr & e) :
  ctx(e.ctx()), formula(e),
  from(e.ctx()), to(e.ctx()),
  euf_component(e.ctx()), octagon_component(e.ctx())
{
  purify();
  euf_component = ctx.bool_val(true);
  octagon_component = ctx.bool_val(true);
  split(formula);
  // euf_component = euf_component.simplify();
  // octagon_component = octagon_component.simplify();
}

Purifier::~Purifier(){
}

void Purifier::traverse(z3::expr & e){
  if (e.is_app()) {
    unsigned num = e.num_args();
    auto f = e.decl();
    
    switch(f.decl_kind()){
    case Z3_OP_AND:{
      for(unsigned i = 0; i < num; i++){
	auto argument = e.arg(i);
	traverse(argument);
      }
      return;
    }
    case Z3_OP_EQ:
    case Z3_OP_DISTINCT:{
      auto lhs = e.arg(0), rhs = e.arg(1);
      e = f(purifyEUFTerm(lhs), purifyEUFTerm(rhs));
      return;
    }
    case Z3_OP_LE:    
    case Z3_OP_GE:
    case Z3_OP_LT:
    case Z3_OP_GT:{
      auto lhs = e.arg(0), rhs = e.arg(1);
      e = f(purifyOctagonTerm(lhs), purifyOctagonTerm(rhs));
      return;
    }
    default:
      throw "Predicate not allowed";
    }
  }
  throw "The expression is not quantifier-free";
}

void Purifier::purify() {
  // POST TODO: Optimize this procedure
  // It seems that there is some redundant work
  // by passing the formula with substitutions again
  while(true){
    traverse(formula);
    
    unsigned num_substitutions = from.size();
    if(num_substitutions == 0)
      return;
    
    formula = formula.substitute(from, to);
    for(unsigned i = 0; i < num_substitutions; i++){
      formula = formula && from[i] == to[i];
    }
      
    from.resize(0);
    to.resize(0);
  }
}

z3::expr Purifier::purifyOctagonTerm(z3::expr & e){
  if(e.is_app()){
    unsigned num = e.num_args();
    auto f = e.decl();
    
    switch(f.decl_kind()){
    case Z3_OP_UMINUS: {
      auto unitary_arg = e.arg(0);
      return f(purifyOctagonTerm(unitary_arg));
    }
    case Z3_OP_ADD:
    case Z3_OP_SUB:
    case Z3_OP_MUL:
    case Z3_OP_DIV:
    case Z3_OP_IDIV:{
      auto lhs = e.arg(0), rhs = e.arg(1);
      return f(purifyOctagonTerm(lhs), purifyOctagonTerm(rhs));
    }
    case Z3_OP_ANUM:
      return e;
    case Z3_OP_UNINTERPRETED:{
      if(num == 0)
	return e;
      
      if(map_euf.find(e.id()) == map_euf.end()){
	std::string fresh_name = "__euf_" + std::to_string(++fresh_var_id);
	auto fresh_constant = ctx.constant(fresh_name.c_str(), f.range());
	map_euf[e.id()] = fresh_var_id;
	// At this point, the top-most symbol of the term e
	// belongs to the EUF signature
	// So we purify e using that signature
	from.push_back(purifyEUFTerm(e));
	to.push_back(fresh_constant);
	return fresh_constant;
      }	
      std::string fresh_name = "__euf_" + std::to_string(map_euf[e.id()]);
      return ctx.constant(fresh_name.c_str(), f.range());
    }
    default:
      throw "The expression doesnt belong to Octagons nor EUF theory";
    }
  }
  throw "The expression is not quantifier-free";
}

z3::expr Purifier::purifyEUFTerm(z3::expr & e){
  if(e.is_app()){
    unsigned num = e.num_args();
    auto f = e.decl();
    
    switch(f.decl_kind()){
    case Z3_OP_UMINUS:
    case Z3_OP_ADD:
    case Z3_OP_SUB:
    case Z3_OP_MUL:
    case Z3_OP_DIV:
    case Z3_OP_IDIV:
      // If we are purifying a euf term and we see a constant
      // Then if such constant is a number, then we `abstract it'
      // Otherwise, we result such constant
    case Z3_OP_ANUM: {
      
      if(map_oct.find(e.id()) == map_oct.end()){
	std::string fresh_name = "__oct_" + std::to_string(++fresh_var_id);
	auto fresh_constant = ctx.constant(fresh_name.c_str(), f.range());
	map_oct[e.id()] = fresh_var_id;
	// At this point, the top-most symbol of the term e
	// belongs to the Octagon signature
	// So we purify e using that signature
	from.push_back(purifyOctagonTerm(e));
	to.push_back(fresh_constant);
	return fresh_constant;
      }
      std::string fresh_name = "__oct_" + std::to_string(map_oct[e.id()]);
      return ctx.constant(fresh_name.c_str(), f.range());
    }
    case Z3_OP_UNINTERPRETED:{
      if(num == 0)
	return e;
      
      z3::expr_vector args(ctx);
      for(unsigned i = 0; i < num; i++){
	auto temp_arg = e.arg(i);
	args.push_back(purifyEUFTerm(temp_arg));
      }
      return f(args);
    }
    default:
      throw "The expression doesnt belong to Octagons nor EUF theory";
    }
  }
  throw "The expression is not quantifier free";
}


void Purifier::split(z3::expr & e){
  unsigned num = e.num_args();
  auto f = e.decl();

  switch(f.decl_kind()){
  case Z3_OP_AND:{
    for(unsigned i = 0; i < num; i++){
      auto argument = e.arg(i);
      split(argument);
    }
    return;
  }
  case Z3_OP_EQ:
  case Z3_OP_DISTINCT:{
      
    switch(e.arg(0).decl().decl_kind()){
    case Z3_OP_UNINTERPRETED:{
      euf_component = euf_component && e;
      return;
    }
    default:{
      octagon_component = octagon_component && e;
      return;
    }
    }
  }
  case Z3_OP_LE:    
  case Z3_OP_GE:
  case Z3_OP_LT:
  case Z3_OP_GT:{
      
    octagon_component = octagon_component && e;
    return;
  }
  default:
    throw "Predicate not allowed";
  }
}

z3::expr Purifier::getEUF(){
  return euf_component;
}

z3::expr Purifier::getOctagon(){
  return octagon_component;
}

std::ostream & operator << (std::ostream & os, Purifier & p){
  os << "EUF-component: " << p.euf_component << std::endl;
  os << "Octagon-component: " << p.octagon_component;
  return os;
}
