#include "DisequalitiesFlattener.h"
#include <z3++.h>

DisequalitiesFlattener::DisequalitiesFlattener(
    z3::expr_vector const & input) :
  ctx(input.ctx()),
  previous_ids({}),
  flatten(ctx), 
  flatten_persistent_from(ctx), 
  flatten_persistent_to(ctx)
{
  for(auto const & formula : input){
    if(formula.is_distinct()){
      auto const & lhs = formula.arg(0);
      auto const & rhs = formula.arg(1);
      updateFlatten(lhs);
      updateFlatten(rhs);
      flatten.push_back(freshConstant(lhs) != freshConstant(rhs));
    }
    else
      flatten.push_back(formula);
  }
}

z3::expr DisequalitiesFlattener::freshConstant(z3::expr const & term){
  if(term.is_const())
    return term;
  return ctx.constant(
      ("_fresh_" + std::to_string(term.id())).c_str(), 
      term.decl().range());
}

void DisequalitiesFlattener::updateFlatten(z3::expr const & term){
  if(term.is_const()) return;
  if(previous_ids.find(term.id()) == previous_ids.end()){
    previous_ids.insert(term.id());
    auto const & fresh_const = freshConstant(term);
    flatten_persistent_from.push_back(fresh_const);
    flatten_persistent_to  .push_back(term);
    flatten.push_back(term == fresh_const);
  }
}

std::ostream & operator << (std::ostream & os, DisequalitiesFlattener const & df){
  return os << z3::mk_and(df.flatten)
    // This substitution removes fresh
    // constants introduced by 
    // DisequalitiesFlattener
    //.substitute(
        //df.flatten_persistent_from, 
        //df.flatten_persistent_to)
    //.simplify()
    ;
}
