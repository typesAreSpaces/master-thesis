#include "OctagonInterpolant.h"

OctagonInterpolant::OctagonInterpolant(z3::expr_vector const & assertions) :
  OctagonParser(assertions), result(assertions.ctx())
{
  // Optional:
  // Sort positions
  
  // Propagate
  for(auto const & var_to_elim : positions){
    for(auto const & pos_position : var_to_elim.first){
      for(auto const & neg_position : var_to_elim.second){
        propagate(pos_position, neg_position);
      }
      // update pos_position to inf (?) MANDATORY: the reason is line 31 
    }
    // update neg_position to inf (?) MANDATORY: the reason is line 31 
  }

  buildInterpolant();
}

void OctagonInterpolant::propagate(UtvpiPosition pos_position, UtvpiPosition neg_position){
  // TODO: keep working here
  // I guess i need to update bounds
  // The latter is done with bounds.insert(position : UtvpiPosition, Bound(bound))
  // We must normalize the octagon in case there is a factor of 2
}

void OctagonInterpolant::buildInterpolant(){
 UtvpiPosition index = 0;
 for(auto const & entry : bounds){
   if(!entry.is_infinite){
     Octagon tmp(index);
     result.push_back(tmp.toZ3Expr(ctx, z3_variables, id_table) 
         <= bounds[index].bound_value);
   }
   index++;
 }
}

z3::expr_vector OctagonInterpolant::getInterpolant() const {
  return result;
}
