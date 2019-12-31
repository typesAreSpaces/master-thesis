#include "Purifier.h"

Purifier::Purifier(z3::expr & e) :
  ctx(e.ctx()), formula(e),
  from(e.ctx()), to(e.ctx())
{
}

Purifier::~Purifier(){
}

z3::expr Purifier::purify() {
  // TODO: Optimize this procedure
  // It seems that there is some redundant work
  // by passing the formula with substitutions again
  while(true){
    traverse(formula);

    unsigned num_substitutions = from.size();
    if(num_substitutions == 0)
      break;
      
    formula = formula.substitute(from, to);
    for(unsigned i = 0; i < num_substitutions; i++)
      formula = formula && from[i] == to[i];
      
    from.resize(0);
    to.resize(0);
  }
  return formula;
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
      break;
    }
    case Z3_OP_EQ:
    case Z3_OP_DISTINCT:{
      auto lhs = e.arg(0), rhs = e.arg(1);      
      e = f(purifyEUFTerm(lhs), purifyEUFTerm(rhs));
      break;
    }
    case Z3_OP_LE:    
    case Z3_OP_GE:
    case Z3_OP_LT:
    case Z3_OP_GT:{
      auto lhs = e.arg(0), rhs = e.arg(1);
      e = f(purifyOctagonTerm(lhs), purifyOctagonTerm(rhs));
      break;
    }
    default:{
      throw "Predicate not allowed";
      break;
    }
    }
  }
  else
    throw "The expression is not quantifier-free";
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
      
      else{
	std::string fresh_name = "__euf" + std::to_string(e.id());
	auto fresh_constant = ctx.constant(fresh_name.c_str(), f.range());
	
	if(id_terms_seen.find(e.id()) == id_terms_seen.end()){
	  id_terms_seen.insert(e.id());
	  // At this point, the top-most symbol of the term e
	  // belongs to the EUF signature
	  // So we purify e using that signature
	  from.push_back(purifyEUFTerm(e));
	  to.push_back(fresh_constant);
	}
	
	return fresh_constant;
      }
    }
    default:
      throw "The expression doesnt belong to Octagons nor EUF theory";
    }
  }
  else 
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

      std::string fresh_name = "__oct" + std::to_string(e.id());
      auto fresh_constant = ctx.constant(fresh_name.c_str(), f.range());
      
      if(id_terms_seen.find(e.id()) == id_terms_seen.end()){
	id_terms_seen.insert(e.id());
	// At this point, the top-most symbol of the term e
	// belongs to the Octagon signature
	// So we purify e using that signature
	from.push_back(purifyOctagonTerm(e));
	to.push_back(fresh_constant);
      }
      
      return fresh_constant;
    }
    case Z3_OP_UNINTERPRETED:{
      if(num == 0)
	return e;
      
      else{
	z3::expr_vector args(ctx);
	for(unsigned i = 0; i < num; i++){
	  auto temp_arg = e.arg(i);
	  args.push_back(purifyEUFTerm(temp_arg));
	}
	return f(args);
      }
    }
    default:
      throw "The expression doesnt belong to Octagons nor EUF theory";
    }
  }
  else 
    throw "The expression is not quantifier free";
}

std::ostream & operator << (std::ostream & os, Purifier & p){
  os << p.formula;
  return os;
}
