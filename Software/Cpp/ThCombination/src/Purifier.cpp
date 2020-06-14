#include "Purifier.h"
#define _DEBUGPURIFIER_ false

unsigned Purifier::fresh_var_id = 0;

Purifier::Purifier(z3::expr const & e) :
  ctx(e.ctx()), 
  oct_component(ctx), euf_component(ctx), 
  map_oct(), map_euf(),
  from(ctx), to(ctx), formula(purify(e))
{
  split(formula);
#if _DEBUGPURIFIER_
  std::cout << *this << std::endl;
#endif
}

z3::expr Purifier::purify(z3::expr const & e){
  z3::expr _formula = traverse(e);
  unsigned num_new_symbols = from.size();
  for(unsigned i = 0; i < num_new_symbols; i++)
    _formula = _formula && from[i] == to[i];
  // "from" and "to" are no longer needed 
  from.resize(0);
  to  .resize(0);
  return _formula;
}

z3::expr Purifier::traverse(z3::expr const & e){
  if (e.is_app()) {
    auto f = e.decl();

    switch(f.decl_kind()){
      case Z3_OP_AND: // FIX: Arity might not be 2 (?)
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
      case Z3_OP_UNINTERPRETED:
        {
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
      case Z3_OP_ANUM: 
        {

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
      case Z3_OP_UNINTERPRETED:
        {
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
    case Z3_OP_AND: // FIX: Arity might not be 2 (?)
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
    case Z3_OP_GT:
      oct_component.push_back(e);
      return;

    default:
      throw "Error @ Purifier::split : Predicate not allowed";
  }
}

void Purifier::addEufFormulasToSolver(z3::solver & s){
  for(auto const & x : euf_component)
    s.add(x);
}

void Purifier::addOctFormulasToSolver(z3::solver & s){
  for(auto const & x : oct_component)
    s.add(x);
}

bool Purifier::inside(z3::expr const & e){
  for(auto const & x : euf_component)
    if(e.id() == x.id())
      return true;
  for(auto const & x : oct_component)
    if(e.id() == x.id())
      return true;
  return false;
}

std::ostream & operator << (std::ostream & os, Purifier & p){
  os << "EUF-component" << std::endl;
  for(auto const & x : p.euf_component)
    os << x << std::endl;
  os << "Octagon-component" << std::endl;
  for(auto const & x : p.oct_component)
    os << x << std::endl;
  return os;
}
