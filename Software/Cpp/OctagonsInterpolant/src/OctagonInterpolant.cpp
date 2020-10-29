#include "OctagonInterpolant.h"

OctagonInterpolant::OctagonInterpolant(z3::expr_vector const & assertions) :
  OctagonParser(assertions), result(assertions.ctx()), num_elims(0)
{
  // Optional:
  // Sort positions
  
  // Elimination
  VarValue var_value_to_elim = 0;
  for(auto const & var_to_elim : positions){
#if _DEBUG_ELIM_
    std::cout << "Removing this var: x_" << var_value_to_elim << std::endl;
    std::cout << "Initial state of bounds" << std::endl;
    std::cout << bounds << std::endl;
#endif
    for(auto const & pos_position : var_to_elim.first){
      for(auto const & neg_position : var_to_elim.second)
        elimination(pos_position, neg_position, var_value_to_elim);
      // update pos_position to inf.
      // The reason is line 178
      bounds.remove(pos_position);
    }
    // update pos_position to inf.
    // The reason is line 178 
    for(auto const & neg_position : var_to_elim.second)
      bounds.remove(neg_position);
    var_value_to_elim++;
  }
  buildInterpolant();
}

void OctagonInterpolant::elimination(UtvpiPosition pos_position, UtvpiPosition neg_position,
    VarValue v){
  num_elims++;
  Octagon oct1(pos_position), oct2(neg_position);
  Bound new_bound = bounds[pos_position] + bounds[neg_position];
#if _DEBUG_ELIM_
  std::cout << "Reducing " << oct1 << " and " << oct2 << std::endl;
#endif
  if(v == oct1.var1.value){
    if(v == oct2.var1.value){
      // -------------------------------------------------------------------------------
      if(oct1.var2.value == oct2.var2.value){ // Same index
        if(oct1.coeff2 == oct2.coeff2){ // Same symbol sign
          new_bound.normalize(2);
          auto new_position = Octagon(oct1.coeff2, oct1.var2.value, ZERO, 0).getUtviPosition();
          bounds.insert(new_position, new_bound);
          updatePositions(oct1.coeff2, oct1.var2, v, new_position);
#if _DEBUG_ELIM_
          std::cout << "Result(1): " << Octagon(oct1.coeff2, oct1.var2.value, ZERO, 0) << std::endl;
#endif
          return;
        }
        else{ // Different symbol sign
          new_bound.normalize(2);
          bounds.insert(0, new_bound); // Update the first inequality (0 <= c) in bounds
#if _DEBUG_ELIM_
          std::cout << "Result(2): " << Octagon(0) << std::endl;
#endif
          return;
        }
      }
      else{ // Different index
        auto new_position = Octagon(oct1.coeff2, oct1.var2.value, oct2.coeff2, oct2.var2.value).getUtviPosition();
        bounds.insert(new_position, new_bound);
        updatePositions(oct1.coeff2, oct1.var2, v, new_position);
        updatePositions(oct2.coeff2, oct2.var2, v, new_position);
#if _DEBUG_ELIM_
        std::cout << "Result(3): " << Octagon(oct1.coeff2, oct1.var2.value, oct2.coeff2, oct2.var2.value) << std::endl;
#endif
        return;
      }
      // -------------------------------------------------------------------------------
    }
    else{
      // -------------------------------------------------------------------------------
      if(oct1.var2.value == oct2.var1.value){ // Same index
        if(oct1.coeff2 == oct2.coeff1){ // Same symbol sign
          new_bound.normalize(2);
          auto new_position = Octagon(oct1.coeff2, oct1.var2.value, ZERO, 0).getUtviPosition();
          bounds.insert(new_position, new_bound);
          updatePositions(oct1.coeff2, oct1.var2, v, new_position);
#if _DEBUG_ELIM_
          std::cout << "Result(4): " << Octagon(oct1.coeff2, oct1.var2.value, ZERO, 0) << std::endl;

#endif
          return;
        }
        else{ // Different symbol sign
          new_bound.normalize(2);
          bounds.insert(0, new_bound); // Update the first inequality (0 <= c) in bounds
#if _DEBUG_ELIM_
          std::cout << "Result(5): " << Octagon(0) << std::endl;
#endif
          return;
        }
      }
      else{ // Different index
        auto new_position = Octagon(oct1.coeff2, oct1.var2.value, oct2.coeff1, oct2.var1.value).getUtviPosition();
        bounds.insert(new_position, new_bound);
        updatePositions(oct1.coeff2, oct1.var2, v, new_position);
        updatePositions(oct2.coeff1, oct2.var1, v, new_position);
#if _DEBUG_ELIM_
        std::cout << "Result(6): " << Octagon(oct1.coeff2, oct1.var2.value, oct2.coeff1, oct2.var1.value) << std::endl;
#endif
        return;
      }
      // -------------------------------------------------------------------------------
    }
  }
  else{
    if(v == oct2.var1.value){
      // -------------------------------------------------------------------------------
      if(oct1.var1.value == oct2.var2.value){ // Same index
        if(oct1.coeff1 == oct2.coeff2){ // Same symbol sign
          new_bound.normalize(2);
          auto new_position = Octagon(oct1.coeff1, oct1.var1.value, ZERO, 0).getUtviPosition();
          bounds.insert(new_position, new_bound);
          updatePositions(oct1.coeff1, oct1.var1, v, new_position);
#if _DEBUG_ELIM_
          std::cout << "Result(7): " << Octagon(oct1.coeff1, oct1.var1.value, ZERO, 0) << std::endl;
#endif
          return;
        }
        else{ // Different symbol sign
          new_bound.normalize(2);
          bounds.insert(0, new_bound); // Update the first inequality (0 <= c) in bounds
#if _DEBUG_ELIM_
          std::cout << "Result(8): " << Octagon(0) << std::endl;
#endif
          return;
        }
      }
      else{ // Different index
        auto new_position = Octagon(oct1.coeff1, oct1.var1.value, oct2.coeff2, oct2.var2.value).getUtviPosition();
        bounds.insert(new_position, new_bound);
        updatePositions(oct1.coeff1, oct1.var1, v, new_position);
        updatePositions(oct2.coeff2, oct2.var2, v, new_position);
#if _DEBUG_ELIM_
        std::cout << "Result(9): " << Octagon(oct1.coeff1, oct1.var1.value, oct2.coeff2, oct2.var2.value) << std::endl;
#endif
        return;
      }
      // -------------------------------------------------------------------------------
    }
    else{
      // -------------------------------------------------------------------------------
      if(oct1.var1.value == oct2.var1.value){ // Same index
        if(oct1.coeff1 == oct2.coeff1){ // Same symbol sign
          new_bound.normalize(2);
          auto new_position = Octagon(oct1.coeff1, oct1.var1.value, ZERO, 0).getUtviPosition();
          bounds.insert(new_position, new_bound);
          updatePositions(oct1.coeff1, oct1.var1, v, new_position);
#if _DEBUG_ELIM_
          std::cout << "Result(10): " << Octagon(oct1.coeff1, oct1.var1.value, ZERO, 0) << std::endl;
#endif
          return;
        }
        else{ // Different symbol sign
          new_bound.normalize(2);
          bounds.insert(0, new_bound); // Update the first inequality (0 <= c) in bounds
#if _DEBUG_ELIM_
          std::cout << "Result(11): " << Octagon(0) << std::endl;
#endif
          return;
        }
      }
      else{ // Different index
        auto new_position = Octagon(oct1.coeff1, oct1.var1.value, oct2.coeff1, oct2.var1.value).getUtviPosition();
        bounds.insert(new_position, new_bound);
        updatePositions(oct1.coeff1, oct1.var1, v, new_position);
        updatePositions(oct2.coeff1, oct2.var1, v, new_position);
#if _DEBUG_ELIM_
        std::cout << "Result(12): " << Octagon(oct1.coeff1, oct1.var1.value, oct2.coeff1, oct2.var1.value) << std::endl;
#endif
        return;
      }
      // -------------------------------------------------------------------------------
    }
  }
}

void OctagonInterpolant::updatePositions(Coeff const & coeff, Var const & var, VarValue const & current_elim_value, UtvpiPosition const & new_position){
#if 1
  if(!is_common_table[var.value] && var.value > current_elim_value){
    switch(coeff){
      case POS:
        positions.insertPositivePosition(var.value, new_position);
        break;
      case NEG:
        positions.insertNegativePosition(var.value, new_position);
        break;
      case ZERO:
        break;
    }
  }
#endif
}

void OctagonInterpolant::buildInterpolant(){
  if(!bounds[0].is_infinite && bounds[0].bound_value < 0)
    result.push_back(ctx.bool_val(false));

  auto entry = bounds.begin();
  // We skip the first entry since if it is a contradiction,
  // line 163-164 takes care of the case and for the rest
  // is not relevant.
  entry++;
  UtvpiPosition index = 1;
  for(; entry != bounds.end(); entry++){
    if(!entry->is_infinite){
      auto z3_octagon = Octagon(index).toZ3Expr(ctx, z3_variables, id_table);
      if(z3_octagon.is_common())
        result.push_back(z3_octagon <= bounds[index].bound_value);
    }
    index++;
  }
}

z3::expr_vector OctagonInterpolant::getInterpolant() const {
  return result;
}
