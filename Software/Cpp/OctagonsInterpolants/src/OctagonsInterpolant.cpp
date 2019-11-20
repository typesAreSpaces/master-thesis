#include "OctagonsInterpolant.h"

OctagonsInterpolant::OctagonsInterpolant(z3::context & ctx, std::istream & in) : ctx(ctx), num_vars(-1) {

  int first_var_position, second_var_position, bound;
  char first_sign, second_sign;

  // Setting INF for all entries in the bounds vector
  bounds.resize(MAX_NUM_INEQS);
  
  positive_var_positions.resize(MAX_NUM_VARS),
    negative_var_positions.resize(MAX_NUM_VARS);
  
  for(auto & it : bounds)
    it = INF;

  // ----------------------------------------------------------------
  // Getting the number of inequalities
  in >> num_inequalities;
  for(int i = 0; i < num_inequalities; ++i){
    in >> first_sign >> first_var_position >> second_sign >> second_var_position >> bound;
    Octagon temp(first_sign, second_sign, first_var_position, second_var_position);
    // -----------------------------------
    // Normalization
    bound = temp.normalize(bound);
    int temp_position = temp.getUtvpiPosition();
    // -----------------------------------
    updatePositions(temp);
    if(first_var_position > num_vars)
      num_vars = first_var_position;
    if(second_var_position > num_vars)
      num_vars = second_var_position;
    bounds[temp_position] = std::min(bounds[temp_position], bound);
  }
  // ----------------------------------------------------------------

  // ----------------------------------------------------------------
  // Getting the number of variables to eliminate
  in >> num_uncomm_vars;
  for(int i = 0; i < num_uncomm_vars; ++i){
    in >> first_var_position;
    variables_to_eliminate.push_back(first_var_position);
  }
  // ----------------------------------------------------------------
}

OctagonsInterpolant::OctagonsInterpolant(const z3::expr & e,
					 const std::vector<std::string> & vars_to_elim) : ctx(e.ctx()){
  unsigned num_ineqs = e.num_args();
  this->num_inequalities = static_cast<int>(num_ineqs);
  this->num_vars = 1;
  int & ref_counter = this->num_vars;
  TablePosition index_map;
  std::vector<std::string> names;
  getSymbols(e, ref_counter, index_map, names);

  int first_var_position, second_var_position, bound;
  char first_sign, second_sign;

  // 2*num_vars*num_vars + 4*num_args + 10 is an upperbound
  // of the number of all the possible utvpis with
  // the given number of variables
  bounds.resize(2*num_vars*num_vars + 4*num_vars + 10);
  positive_var_positions.resize(num_vars),
    negative_var_positions.resize(num_vars);
  
  for(auto & it : bounds)
    it = INF;
  
  // ----------------------------------------------------------------
  // Getting the number of inequalities
  for(unsigned i = 0; i < num_ineqs; ++i){
    auto current_utvpi = e.arg(i);
    auto lhs = current_utvpi.arg(0);
    auto rhs = current_utvpi.arg(1);
    auto current_pred_name = current_utvpi.decl().name().str();
    bound = rhs.get_numeral_int();
    
    switch(lhs.num_args()){
    case 0:
      // One variable
      if(current_pred_name == "<=")
	first_sign = '+';
      else if (current_pred_name == ">="){
	first_sign = '-';
	bound = -bound;
      }
      else throw "Not an utvpi formula";
      first_var_position = index_map[lhs.id()];
      second_sign = '+';
      second_var_position = -1;
      break;
    case 2:
      // Two variables
      switch(lhs.arg(0).num_args()){
      case 0:
	first_var_position = index_map[lhs.arg(0).id()];
	first_sign = '+';
	break;
      case 2:
	first_var_position = index_map[lhs.arg(0).arg(1).id()];
	first_sign = '-';
	break;
      default:
	throw "Not an utvpi formula";
	break;
      }
      switch(lhs.arg(1).num_args()){
      case 0:
	second_var_position = index_map[lhs.arg(1).id()];
	second_sign = '+';
	break;
      case 2:
	second_var_position = index_map[lhs.arg(1).arg(1).id()];
	second_sign = '-';
	break;
      default:
	throw "Not an utvpi formula";
	break;
      }
      break;
    default:
      throw "Not an utvpi formula";
      break;
    }
    // ----------------------------------------------------------------
    Octagon temp(first_sign, second_sign, first_var_position, second_var_position);
    // -----------------------------------
    // Normalization
    bound = temp.normalize(bound);
    int temp_position = temp.getUtvpiPosition();
    // -----------------------------------
    updatePositions(temp);
    bounds[temp_position] = std::min(bounds[temp_position], bound);
  }
  // ----------------------------------------------------------------

  // ----------------------------------------------------------------
  // Getting the number of variables to eliminate
  this->num_uncomm_vars = static_cast<int>(vars_to_elim.size());
  for(auto var_to_elim : vars_to_elim)
    variables_to_eliminate.push_back(index_map[ctx.int_const(var_to_elim.c_str()).id()]);
  // ----------------------------------------------------------------
  this->names = names;
}

OctagonsInterpolant::~OctagonsInterpolant(){}

void OctagonsInterpolant::updatePositions(Octagon & f){
  char first_sign = f.getFirstSign(), second_sign = f.getSecondSign();
  int first_var_position = f.getFirstVarPosition(), second_var_position = f.getSecondVarPosition();
  int f_position = f.getUtvpiPosition();

  // Only perform the update operation if
  // the octagon is not of the form 0 <= a (i.e. with position different from 0)
  if(f_position > 0){
    switch(first_sign){
    case '+':
      positive_var_positions[first_var_position].push_back(f_position);
      break;
    case '-':
      negative_var_positions[first_var_position].push_back(f_position);
      break;
    default:
      throw "Error sign with the first sign";
      break;
    }
    // Only perform the update operation on the second position if
    // the octagon is of the form +/- x +/- y <= b
    // (i.e. the second_var_position is not equal to -1)
    if(second_var_position != -1){
      switch(second_sign){
      case '+':
	positive_var_positions[second_var_position].push_back(f_position);
	break;
      case '-':
	negative_var_positions[second_var_position].push_back(f_position);
	break;
      default:
	throw "Error sign with the second sign";
	break;
      }
    }
  }
}

void OctagonsInterpolant::printMessage(Octagon & x, Octagon & y, Octagon & z){
  std::cout << "Taking inequalities:" << std::endl;
  std::cout << x;
  std::cout << " <= " << bounds[x.getUtvpiPosition()] << std::endl;
  std::cout << y;
  std::cout << " <= " << bounds[y.getUtvpiPosition()] << std::endl;
  std::cout << "To produce this" << std::endl;
  std::cout << z;
  std::cout << " <= " << bounds[z.getUtvpiPosition()] << std::endl << std::endl;
}

// Precondition Octagon & x and Octagon & y have num_args = 2
void OctagonsInterpolant::operateBoth2Args(int var_to_elim, Octagon & x, Octagon & y){
  char first_sign_x = x.getFirstSign(), second_sign_x = x.getSecondSign();
  char first_sign_y = y.getFirstSign(), second_sign_y = y.getSecondSign();
  char first_sign, second_sign;
  
  int first_var_position_x = x.getFirstVarPosition(), second_var_position_x = x.getSecondVarPosition();
  int first_var_position_y = y.getFirstVarPosition(), second_var_position_y = y.getSecondVarPosition();
  int first_var_position, second_var_position;
  
  int bound_x = bounds[x.getUtvpiPosition()], bound_y = bounds[y.getUtvpiPosition()];
  // TODO: Keep working here
  
  // Case +/- x (...); -/+ x (...) 
  if(first_var_position_x == first_var_position_y && first_var_position_x == var_to_elim){
    // Case +/- x +/- y <= b1; -/+ x +/- y <= b2
    if(second_sign_x == second_sign_y && second_var_position_x == second_var_position_y){
      Octagon temp(second_sign_x, '+', second_var_position_x, -1);
      int temp_position = temp.getUtvpiPosition();
      bounds[temp_position] = std::min(bounds[temp_position], (bound_x + bound_y)/2);
      updatePositions(temp);
#if PRINT_MSG
      printMessage(x, y, temp);
#endif
    }
    // Case +/- x +/- y <= b1; -/+ x -/+ y <= b2
    else if(second_sign_x != second_sign_y && second_var_position_x == second_var_position_y){
      bounds[0] = std::min(bounds[0], bound_x + bound_y);
#if PRINT_MSG
      std::cout << "Couldn't produce anything interesting (0 <= a)" << std::endl << std::endl;
#endif
    }
    // Case +/- x first_sign y1 <= b1; -/+ x second_sign y2 <= b2; (with y1 != y2) 
    else{
      // Reorder as necessary so
      // first_sign y1 second_sign y2 <= b (with y1 > y2)
      if(second_var_position_x > second_var_position_y){
	first_sign = second_sign_x;
	first_var_position = second_var_position_x;
	second_sign = second_sign_y;
	second_var_position = second_var_position_y;
      }
      else{
	second_sign = second_sign_x;
	second_var_position = second_var_position_x;
	first_sign = second_sign_y;
	first_var_position = second_var_position_y;
      }
      Octagon temp(first_sign, second_sign, first_var_position, second_var_position);
      int temp_position = temp.getUtvpiPosition();
      bounds[temp_position] = std::min(bounds[temp_position], bound_x + bound_y);
      updatePositions(temp);
#if PRINT_MSG
      printMessage(x, y, temp);
#endif
    }
  }
  
  // Case +/- x (...); (..) -/+ x (..)
  else if(first_var_position_x == second_var_position_y && first_var_position_x == var_to_elim){
    // Case +/- x +/- y <= b1; +/- y -/+ x <= b2
    if(second_sign_x == first_sign_y && second_var_position_x == first_var_position_y){
      Octagon temp(second_sign_x, '+', second_var_position_x, -1);
      int temp_position = temp.getUtvpiPosition();
      bounds[temp_position] = std::min(bounds[temp_position], (bound_x + bound_y)/2);
      updatePositions(temp);
#if PRINT_MSG
      printMessage(x, y, temp);
#endif
    }
    // Case +/- x +/- y <= b1; -/+ y -/+ x <= b2
    else if(second_sign_x != first_sign_y && second_var_position_x == first_var_position_y){
      bounds[0] = std::min(bounds[0], bound_x + bound_y);
#if PRINT_MSG
      std::cout << "Couldn't produce anything interesting (0 <= a)" << std::endl << std::endl;
#endif
    }
    // Case +/- x first_sign y1 <= b1; second_sign y2 -/+ x <= b2; (with y1 != y2) 
    else{
      // Reorder as necessary so
      // first_sign y1 second_sign y2 <= b (with y1 > y2)
      if(second_var_position_x > first_var_position_y){
	first_sign = second_sign_x;
	first_var_position = second_var_position_x;
	second_sign = first_sign_y;
	second_var_position = first_var_position_y;
      }
      else{
	second_sign = second_sign_x;
	second_var_position = second_var_position_x;
	first_sign = first_sign_y;
	first_var_position = first_var_position_y;
      }
      Octagon temp(first_sign, second_sign, first_var_position, second_var_position);
      int temp_position = temp.getUtvpiPosition();
      bounds[temp_position] = std::min(bounds[temp_position], bound_x + bound_y);
      updatePositions(temp);
#if PRINT_MSG
      printMessage(x, y, temp);
#endif
    }
  }
  
  // Case (...) +/- x (...); -/+ x (...)
  else if(second_var_position_x == first_var_position_y && second_var_position_x == var_to_elim){
    // Case +/- y +/- x <= b1; -/+ x +/- y <= b2
    if(first_sign_x == second_sign_y && first_var_position_x == second_var_position_y){
      Octagon temp(first_sign_x, '+', first_var_position_x, -1);
      int temp_position = temp.getUtvpiPosition();
      bounds[temp_position] = std::min(bounds[temp_position], (bound_x + bound_y)/2);
      updatePositions(temp);
#if PRINT_MSG
      printMessage(x, y, temp);
#endif
    }
    // Case +/- y +/- x <= b1; -/+ x -/+ y <= b2
    else if(first_sign_x != second_sign_y && first_var_position_x == second_var_position_y){
      bounds[0] = std::min(bounds[0], bound_x + bound_y);
#if PRINT_MSG
      std::cout << "Couldn't produce anything interesting (0 <= a)" << std::endl << std::endl;
#endif
    }
    // Case first_sign y1 +/- x <= b1; -/+ x second_sign y2 <= b2; (with y1 != y2)
    else{
      // Reorder as necessary so
      // first_sign y1 second_sign y2 <= b (with y1 > y2)
      if(first_var_position_x > second_var_position_y){
	first_sign = first_sign_x;
	first_var_position = first_var_position_x;
	second_sign = second_sign_y;
	second_var_position = second_var_position_y;
      }
      else{
	second_sign = first_sign_x;
	second_var_position = first_var_position_x;
	first_sign = second_sign_y;
	first_var_position = second_var_position_y;
      }
      Octagon temp(first_sign, second_sign, first_var_position, second_var_position);
      int temp_position = temp.getUtvpiPosition();
      bounds[temp_position] = std::min(bounds[temp_position], bound_x + bound_y);
      updatePositions(temp);
#if PRINT_MSG
      printMessage(x, y, temp);
#endif
    }
  }
  
  // Case (...) +/- x (...); (...) -/+ x (...)
  else if(second_var_position_x == second_var_position_y && second_var_position_x == var_to_elim){
    // Case +/- y +/- x <= b1; +/- y -/+ x <= b2
    if(first_sign_x == first_sign_y && first_var_position_x == first_var_position_y){
      Octagon temp(first_sign_x, '+', first_var_position_x, -1);
      int temp_position = temp.getUtvpiPosition();
      bounds[temp_position] = std::min(bounds[temp_position], (bound_x + bound_y)/2);
      updatePositions(temp);
#if PRINT_MSG
      printMessage(x, y, temp);
#endif
    }
    // Case +/- y +/- x <= b1; -/+ y -/+ x <= b2
    else if(first_sign_x != first_sign_y && first_var_position_x == first_var_position_y){
      bounds[0] = std::min(bounds[0], bound_x + bound_y);
#if PRINT_MSG
      std::cout << "Couldn't produce anything interesting (0 <= a)" << std::endl << std::endl;
#endif
    }
    // Case first_sign y1 +/- x <= b1; second_sign y2 -/+ x <= b2; (with y1 != y2)
    else{
      // Reorder as necessary so
      // first_sign y1 second_sign y2 <= b (with y1 > y2)
      if(first_var_position_x > first_var_position_y){
	first_sign = first_sign_x;
	first_var_position = first_var_position_x;
	second_sign = first_sign_y;
	second_var_position = first_var_position_y;
      }
      else{
	second_sign = first_sign_x;
	second_var_position = first_var_position_x;
	first_sign = first_sign_y;
	first_var_position = first_var_position_y;
      }
      Octagon temp(first_sign, second_sign, first_var_position, second_var_position);
      int temp_position = temp.getUtvpiPosition();
      bounds[temp_position] = std::min(bounds[temp_position], bound_x + bound_y);
      updatePositions(temp);
#if PRINT_MSG
      printMessage(x, y, temp);
#endif
    }
  }
}

void OctagonsInterpolant::operateBoth1Arg(int var_to_elim, Octagon & x, Octagon & y){  
  int first_var_position_x = x.getFirstVarPosition();
  int first_var_position_y = y.getFirstVarPosition();
  
  int bound_x = bounds[x.getUtvpiPosition()], bound_y = bounds[y.getUtvpiPosition()];

  // Case +/- x (-1); -/+ x + (-1) 
  if(first_var_position_x == first_var_position_y && first_var_position_x == var_to_elim)
    bounds[0] = std::min(bounds[0], bound_x + bound_y);
}

void OctagonsInterpolant::operate2Args1Arg(int var_to_elim, Octagon & x, Octagon & y){
  char second_sign_x = x.getSecondSign();
  
  int first_var_position_x = x.getFirstVarPosition(), second_var_position_x = x.getSecondVarPosition();
  int first_var_position_y = y.getFirstVarPosition();
  
  int bound_x = bounds[x.getUtvpiPosition()], bound_y = bounds[y.getUtvpiPosition()];
  
  // Case +/- x (...); -/+ x + (-1) 
  if(first_var_position_x == first_var_position_y && first_var_position_x == var_to_elim){
    Octagon temp(second_sign_x, '+', second_var_position_x, -1);
    int temp_position = temp.getUtvpiPosition();
    bounds[temp_position] = std::min(bounds[temp_position], bound_x + bound_y);
    updatePositions(temp);
#if PRINT_MSG
    printMessage(x, y, temp);
#endif
  }
}

void OctagonsInterpolant::getSymbols(const z3::expr & formula, int & counter,
				     TablePosition & table, std::vector<std::string> & names){  
  auxiliarGetSymbols(formula, counter, table, names);
  for(auto it : table)
    --table[it.first];
  --counter;
}

void OctagonsInterpolant::auxiliarGetSymbols(const z3::expr & e, int & counter,
					     TablePosition & table, std::vector<std::string> & names){
  if (e.is_app()){
    unsigned num = e.num_args();
    if(num == 0 && e.decl().decl_kind() != Z3_OP_ANUM && table[e.id()] == 0){
      table[e.id()] = counter++;
      names.push_back(e.decl().name().str());
    }
    for (unsigned i = 0; i < num; ++i)
      auxiliarGetSymbols(e.arg(i), counter, table, names);
  }
}

z3::expr OctagonsInterpolant::buildInterpolant(){
      
#if PRINT_INTER
  std::cout << "Initial (encoded) UTVPI system" << std::endl;
  int max_num_ineqs = 2*(num_vars+1)*(num_vars+1);
  for(int i = 0; i < max_num_ineqs; ++i){
    if(bounds[i] != INF){
      Octagon temp = Octagon(i);
      std::cout << temp;
      std::cout << " <= " << bounds[i] << std::endl;
    }
  }
  std::cout << std::endl;
#endif
  // ----------------------------------------------------------------------------------------------------------------
  // Interpolation Algorithm
  for(auto var_to_eliminate : variables_to_eliminate){
#if PRINT_INTER
    std::cout << "Eliminating variable x_" << var_to_eliminate << "\n";
#endif
    for(auto x : positive_var_positions[var_to_eliminate])
      for(auto y : negative_var_positions[var_to_eliminate]){
	if(bounds[x] != INF && bounds[y] != INF){
	  Octagon first_octagon = Octagon(x);
	  Octagon second_octagon = Octagon(y);
	  if(first_octagon.num_args() == 1){
	    if(second_octagon.num_args() == 1)
	      operateBoth1Arg(var_to_eliminate, second_octagon, first_octagon);
	    else
	      operate2Args1Arg(var_to_eliminate, second_octagon, first_octagon);
	  }
	  else{
	    if(second_octagon.num_args() == 1)
	      operate2Args1Arg(var_to_eliminate, first_octagon, second_octagon);
	    else
	      operateBoth2Args(var_to_eliminate, first_octagon, second_octagon);
	  }
	}
      }

    // 'Delete' in positive_var_positions
    // the variable just eliminated
    for(auto index : positive_var_positions[var_to_eliminate])
      bounds[index] = INF;
    
    // 'Delete' in negative_var_positions
    // the variable just eliminated
    for(auto index : negative_var_positions[var_to_eliminate])
      bounds[index] = INF;

#if PRINT_INTER
    std::cout << "After Eliminating Variable x_" << var_to_eliminate << "\n";
    for(int i = 0; i < max_num_ineqs; ++i)
      if(bounds[i] != INF){
	Octagon temp = Octagon(i);
	std::cout << temp;
	std::cout << " <= " << bounds[i] << "\n";
      }
    std::cout << std::endl;
#endif
  }

  z3::expr_vector result_vect(ctx);

  for(int i = 0; i < max_num_ineqs; ++i){
    if(bounds[i] != INF){
      Octagon temp = Octagon(i);
      
      char first_sign = temp.getFirstSign(), second_sign = temp.getSecondSign();
      int first_var_position = temp.getFirstVarPosition(), second_var_position = temp.getSecondVarPosition();
      
      switch(temp.num_args()){
      case 0:
	return ctx.bool_val(false);
      case 1:
	{
	  if(first_sign == '+')
	    result_vect.push_back(ctx.int_const(names[first_var_position].c_str()) <= bounds[i]);
	  else if(first_sign == '-')
	    result_vect.push_back((-1 * ctx.int_const(names[first_var_position].c_str())) <= bounds[i]);
	}
	break;
      case 2:
	{
	  if(first_sign == '+' && second_sign == '+')
	    result_vect.push_back((ctx.int_const(names[first_var_position].c_str()) + ctx.int_const(names[second_var_position].c_str())) <= bounds[i]);
	  else if(first_sign == '+' && second_sign == '-')
	    result_vect.push_back((ctx.int_const(names[first_var_position].c_str()) + (-1 * ctx.int_const(names[second_var_position].c_str()))) <= bounds[i]);    
	  else if(first_sign == '-' && second_sign == '+')
	    result_vect.push_back(((-1 * ctx.int_const(names[first_var_position].c_str())) + ctx.int_const(names[second_var_position].c_str())) <= bounds[i]);
	  else if(first_sign == '-' && second_sign == '-')
	    result_vect.push_back(((-1 * ctx.int_const(names[first_var_position].c_str())) + (-1 * ctx.int_const(names[second_var_position].c_str()))) <= bounds[i]);
	}
	break;
      }
    }
  }
  
  return mk_and(result_vect);
  // ----------------------------------------------------------------------------------------------------------------
}
