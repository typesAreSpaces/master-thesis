#include "Purifier.h"
#define _DEBUGPURIFIER_ true

unsigned Purifier::fresh_var_id = 0;

Purifier::Purifier(z3::expr const & e) :
  ctx(e.ctx()), formula(e.ctx()),
  euf_component(e.ctx()), oct_component(e.ctx()),
  from(e.ctx()), to(e.ctx()){
  purify(e);
  split(formula);
#if _DEBUGPURIFIER_
  std::cout << *this << std::endl;
#endif
}

Purifier::~Purifier(){
}

void Purifier::purify(z3::expr const & e) {
  formula = traverse(e);
  unsigned num_substitutions = from.size();
  for(unsigned i = 0; i < num_substitutions; i++)
    formula = formula && from[i] == to[i];
  from.resize(0);
  to.resize(0);
}

z3::expr Purifier::traverse(z3::expr const & e){
  if (e.is_app()) {
    auto f = e.decl();
    
    switch(f.decl_kind()){
    case Z3_OP_AND:
      return f(traverse(e.arg(0)), traverse(e.arg(1)));
    case Z3_OP_EQ:
    case Z3_OP_DISTINCT:
      return f(purifyEUFTerm(e.arg(0)), purifyEUFTerm(e.arg(1)));
    case Z3_OP_LE:    
    case Z3_OP_GE:
    case Z3_OP_LT:
    case Z3_OP_GT:
      return f(purifyOctagonTerm(e.arg(0)), purifyOctagonTerm(e.arg(1)));
    default:
      throw "Predicate not allowed";
    }
  }
  throw "The expression is not quantifier-free";
}

z3::expr Purifier::purifyOctagonTerm(z3::expr const & e){
  if(e.is_app()){
    unsigned num = e.num_args();
    auto f = e.decl();
    
    switch(f.decl_kind()){
    case Z3_OP_UMINUS:
      return f(purifyOctagonTerm(e.arg(0)));
    case Z3_OP_ADD:
    case Z3_OP_SUB:
    case Z3_OP_MUL:
    case Z3_OP_DIV:
    case Z3_OP_IDIV:
      return f(purifyOctagonTerm(e.arg(0)), purifyOctagonTerm(e.arg(1)));
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

z3::expr Purifier::purifyEUFTerm(z3::expr const & e){
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
	args.push_back(purifyEUFTerm(e.arg(i)));
      }
      return f(args);
    }
    default:
      throw "The expression doesnt belong to Octagons nor EUF theory";
    }
  }
  throw "The expression is not quantifier free";
}


void Purifier::split(z3::expr const & e){
  auto f = e.decl();

  switch(f.decl_kind()){
  case Z3_OP_AND:
    split(e.arg(0));
    split(e.arg(1));
    return;
  case Z3_OP_EQ:
  case Z3_OP_DISTINCT:
    // We check the lhs of the equation/disequation
    // because we keep the old term "from" on that
    // side
    switch(e.arg(0).decl().decl_kind()){
    case Z3_OP_UNINTERPRETED:
      euf_component.push_back(e);
      return;
    default:
      oct_component.push_back(e);
      return;
    }
  case Z3_OP_LE:    
  case Z3_OP_GE:
  case Z3_OP_LT:
  case Z3_OP_GT:{
    oct_component.push_back(e);
    return;
  }
  default:
    throw "Predicate not allowed";
  }
}

z3::expr Purifier::purifyEUFEq(z3::expr const & eq){
  auto f = eq.decl();
  switch(f.decl_kind()){
  case Z3_OP_EQ:
    return f(purifyEUFTerm(eq.arg(0)), purifyEUFTerm(eq.arg(1)));
  default:
    throw "Not an equality";
  }
}

z3::expr Purifier::purifyOctEq(z3::expr const & eq){
  auto f = eq.decl();
  switch(f.decl_kind()){
  case Z3_OP_EQ:
    return f(purifyOctagonTerm(eq.arg(0)), purifyOctagonTerm(eq.arg(1)));
  default:
    throw "Not an equality";
  }
}

std::ostream & operator << (std::ostream & os, Purifier & p){
  os << "EUF-component" << std::endl;
  unsigned num = p.euf_component.size();
  for(unsigned i = 0; i < num; i++)
    os << p.euf_component[i] << std::endl;
  os << "Octagon-component" << std::endl;
  num = p.oct_component.size();
  for(unsigned i = 0; i < num; i++)
    os << p.oct_component[i] << std::endl;
  return os;
}
