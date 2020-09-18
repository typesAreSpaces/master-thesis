#include "Purifier.h"
#define _DEBUGPURIFIER_ 0

unsigned Purifier::fresh_var_id = 0;

Purifier::Purifier(z3::expr_vector const & e) :
  //fresh_var_id(0),
  ctx(e.ctx()), 
  oct_component(ctx), euf_component(ctx), 
  oct_fresh_ids(), euf_fresh_ids(),
  from(ctx), to(ctx), 
  persistent_from(ctx), persistent_to(ctx), 
  input(purify(e))
{
  split(input);
#if _DEBUGPURIFIER_
  std::cout << *this << std::endl;
#endif

#if _DEBUG_SHARING_
  std::cout << "Shared variables" << std::endl;
  std::cout << shared_variables << std::endl;
  std::cout << "OCT component" << std::endl;
  std::cout << oct_component << std::endl;
  std::cout << "EUF component" << std::endl;
  std::cout << euf_component << std::endl;
#endif
}

z3::expr_vector Purifier::purify(z3::expr_vector const & assertions){
  z3::expr_vector result(assertions.ctx());
  for(auto const & assertion : assertions)
    result.push_back(purify(assertion));
  return result;
}

z3::expr Purifier::purify(z3::expr const & e){
  z3::expr _input = traverse(e);
  unsigned num_new_symbols = from.size();
  for(unsigned i = 0; i < num_new_symbols; i++){
    _input = _input && from[i] == to[i];
    persistent_from.push_back(from[i]);
    persistent_to.push_back(to[i]);
  }
  // "from" and "to" are no longer needed 
  from.resize(0);
  to  .resize(0);
  return _input;
}

z3::expr Purifier::traverse(z3::expr const & e){
  if (e.is_app()) {
    auto f = e.decl();

    switch(f.decl_kind()){
      case Z3_OP_AND: 
        {
          z3::expr_vector args(ctx);
          unsigned num_args = e.num_args();
          for(unsigned _i = 0; _i < num_args; ++_i)
            args.push_back(traverse(e.arg(_i)));
          return z3::mk_and(args);
          //return f(traverse(e.arg(0)), traverse(e.arg(1)));
        }
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
          if(euf_fresh_ids.find(term.id()) == euf_fresh_ids.end()){
#ifdef ADD_COMMON_PREFIX
            std::string fresh_name;
            if(term.is_common())
              fresh_name = PREFIX_COMM_EUF + std::to_string(++fresh_var_id);
            else if(term.is_a_strict())
              fresh_name = PREFIX_A_EUF + std::to_string(++fresh_var_id);
            else
              fresh_name = PREFIX_B_EUF + std::to_string(++fresh_var_id);
#else
            std::string fresh_name = PREFIX_EUF + std::to_string(++fresh_var_id);
#endif
            auto fresh_constant = ctx.constant(fresh_name.c_str(), f.range());
            euf_fresh_ids[term.id()] = fresh_var_id;
            // At this point, the top-most symbol of the term e
            // belongs to the EUF signature
            // So we purify e using that signature
            from.push_back(purifyEUFTerm(term));
            to.push_back(fresh_constant);
            return fresh_constant;
          }	
#ifdef ADD_COMMON_PREFIX
          std::string fresh_name;
          if(term.is_common())
            fresh_name = PREFIX_COMM_EUF + std::to_string(euf_fresh_ids[term.id()]);
          else if(term.is_a_strict())
            fresh_name = PREFIX_A_EUF + std::to_string(euf_fresh_ids[term.id()]);
          else
            fresh_name = PREFIX_B_EUF + std::to_string(euf_fresh_ids[term.id()]);


#else
          std::string fresh_name = PREFIX_EUF + std::to_string(euf_fresh_ids[term.id()]);
#endif
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
          if(oct_fresh_ids.find(term.id()) == oct_fresh_ids.end()){
#ifdef ADD_COMMON_PREFIX
            std::string fresh_name;
            if(term.is_common())
              fresh_name = PREFIX_COMM_OCT + std::to_string(++fresh_var_id);
            else if(term.is_a_strict())
              fresh_name = PREFIX_A_OCT + std::to_string(++fresh_var_id);
            else
              fresh_name = PREFIX_B_OCT + std::to_string(++fresh_var_id);
#else
            std::string fresh_name = PREFIX_OCT + std::to_string(++fresh_var_id);
#endif
            auto fresh_constant = ctx.constant(fresh_name.c_str(), f.range());
            oct_fresh_ids[term.id()] = fresh_var_id;

            // At this point, the top-most symbol of the term e
            // belongs to the Octagon signature
            // So we purify e using that signature
            from.push_back(purifyOctagonTerm(term));
            to.push_back(fresh_constant);
            return fresh_constant;
          }
#ifdef ADD_COMMON_PREFIX
          std::string fresh_name;
          if(term.is_common())
            fresh_name = PREFIX_COMM_OCT + std::to_string(oct_fresh_ids[term.id()]);
          else if(term.is_a_strict())
            fresh_name = PREFIX_A_OCT + std::to_string(oct_fresh_ids[term.id()]);
          else
            fresh_name = PREFIX_B_OCT + std::to_string(oct_fresh_ids[term.id()]);
#else
          std::string fresh_name = PREFIX_OCT + std::to_string(oct_fresh_ids[term.id()]);
#endif
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

void Purifier::split(z3::expr_vector const & e){
  for(auto const & entry : e)
    split(entry);
}

void Purifier::split(z3::expr const & e){
  if(e.is_app()){
    auto f = e.decl();

    switch(f.decl_kind()){
      case Z3_OP_AND: 
        {
          unsigned num_args = e.num_args();
          for(unsigned _i = 0; _i < num_args; ++_i)
            split(e.arg(_i));
        }
        return;
      case Z3_OP_EQ:
      case Z3_OP_DISTINCT:
        // If both elements are constants, then it should 
        // go to the oct component
        if(e.arg(0).is_const() && e.arg(1).is_const()){
          oct_component.push_back(e);
          return;
        }
        else
          // We check the lhs of the equation/disequation
          // because we keep the old term "from" is on that
          // side
          switch(e.arg(0).decl().decl_kind()){
            case Z3_OP_UNINTERPRETED:
              euf_component.push_back(e);
              return;
            default:
              oct_component.push_back(e);
              //return;
          }
      case Z3_OP_LE:    
      case Z3_OP_GE:
      case Z3_OP_LT:
      case Z3_OP_GT:
        oct_component.push_back(e);
        return;

      default:
        throw "Error @ Purifier::split :" 
          "Predicate not allowed";
    }
  }
  throw "Error @ Purifier::split :" 
    "The expression is not an application";
}

z3::expr_vector const Purifier::getOctComponent() const {
  return oct_component;
}

z3::expr_vector const Purifier::getEufComponent() const {
  return euf_component;
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
