#include "Purifier.h"
#define _DEBUGPURIFIER_ false

unsigned Purifier::fresh_var_id = 0;

Purifier::Purifier(z3::expr const & e) :
  ctx(e.ctx()), formula(ctx),
  euf_component(ctx), oct_component(ctx),
  from(ctx), to(ctx){

  try{
    purify(e);
  }
  catch(char const * e){
    std::cout << e << std::endl;
  }
  
  try{
    split(formula);
  }
  catch(char const * e){
    std::cout << e << std::endl;
  }
  
#if _DEBUGPURIFIER_
  std::cout << *this << std::endl;
#endif
}

void Purifier::purify(z3::expr const & e){
  formula = traverse(e);
  unsigned num_new_symbols = from.size();
  for(unsigned i = 0; i < num_new_symbols; i++)
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
      std::cout << e << std::endl;
      throw "Error @ Purifier::traverse : Predicate not allowed in QF_UFLIA";
    }
  }
  throw "Error @ Purifier::traverse : The expression is not a conjunction of quantifier-free formulas";
}

z3::expr Purifier::purifyOctagonTerm(z3::expr const & term){
  if(term.is_app()){
    unsigned num = term.num_args();
    auto f = term.decl();
    
    switch(f.decl_kind()){
    case Z3_OP_UMINUS:
      return f(purifyOctagonTerm(term.arg(0)));
    case Z3_OP_ADD:
    case Z3_OP_SUB:
    case Z3_OP_MUL:
    case Z3_OP_DIV:
    case Z3_OP_IDIV:
      return f(purifyOctagonTerm(term.arg(0)), purifyOctagonTerm(term.arg(1)));
    case Z3_OP_ANUM:
      return term;
    case Z3_OP_UNINTERPRETED:{
      if(num == 0)
	return term;
      
      if(map_euf.find(term.id()) == map_euf.end()){
	std::string fresh_name = "euf_" + std::to_string(++fresh_var_id);
	auto fresh_constant = ctx.constant(fresh_name.c_str(), f.range());
	map_euf[term.id()] = fresh_var_id;
	// At this point, the top-most symbol of the term e
	// belongs to the EUF signature
	// So we purify e using that signature
	from.push_back(purifyEUFTerm(term));
	to.push_back(fresh_constant);
	return fresh_constant;
      }	
      std::string fresh_name = "euf_" + std::to_string(map_euf[term.id()]);
      return ctx.constant(fresh_name.c_str(), f.range());
    }
    default:
      throw "Error @ Purifier::purifyOctagonTerm : The expression doesnt belong to Octagons nor EUF theory";
    }
  }
  throw "Error @ Purifier::purifyOctagonTerm : The expression is not quantifier-free";
}

z3::expr Purifier::purifyEUFTerm(z3::expr const & term){
  if(term.is_app()){
    unsigned num = term.num_args();
    auto f = term.decl();
    
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
      
      if(map_oct.find(term.id()) == map_oct.end()){
	std::string fresh_name = "oct_" + std::to_string(++fresh_var_id);
	auto fresh_constant = ctx.constant(fresh_name.c_str(), f.range());
	map_oct[term.id()] = fresh_var_id;
	
	// At this point, the top-most symbol of the term e
	// belongs to the Octagon signature
	// So we purify e using that signature
	from.push_back(purifyOctagonTerm(term));
	to.push_back(fresh_constant);
	return fresh_constant;
      }
      std::string fresh_name = "oct_" + std::to_string(map_oct[term.id()]);
      return ctx.constant(fresh_name.c_str(), f.range());
    }
    case Z3_OP_UNINTERPRETED:{
      if(num == 0)
	return term;
      
      z3::expr_vector args(ctx);
      for(unsigned i = 0; i < num; i++)
	args.push_back(purifyEUFTerm(term.arg(i)));
      
      return f(args);
    }
    default:
      throw "Error @ Purifier::purifyEUFTerm : The expression doesnt belong to Octagons nor EUF theory";
    }
  }
  throw "Error @ Purifier::purifyEUFTerm : The expression is not quantifier free";
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
    throw "Error @ Purifier::split : Predicate not allowed";
  }
}

void Purifier::addEufFormulasToSolver(z3::solver & s){
  unsigned size = euf_component.size();
  for(unsigned i = 0; i < size; i++)
    s.add(euf_component[i]);
}

void Purifier::addOctFormulasToSolver(z3::solver & s){
  unsigned size = oct_component.size();
  for(unsigned i = 0; i < size; i++)
    s.add(oct_component[i]);
}

bool Purifier::inside(z3::expr const & e){
  unsigned num = euf_component.size();
  for(unsigned i = 0; i < num; i++)
    if(e.id() == euf_component[i].id())
      return true;
  num = oct_component.size();
  for(unsigned i = 0; i < num; i++)
    if(e.id() == oct_component[i].id())
      return true;
  return false;
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
