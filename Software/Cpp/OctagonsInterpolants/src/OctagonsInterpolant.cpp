#include "OctagonsInterpolant.h"

OctagonsInterpolant::OctagonsInterpolant(std::istream & in) : num_vars(-1) {

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
    std::cout << first_sign << " " << first_var_position << " " << second_sign << " " << second_var_position << " " << bound << std::endl;
    Octagon temp(first_sign, second_sign, first_var_position, second_var_position);
    // -----------------------------------
    // Normalization
    bound = temp.normalize(bound);
    // -----------------------------------
    std::cout << temp << std::endl;
    std::cout << temp.getUtvpiPosition() << std::endl;
    updatePositions(temp);
    if(first_var_position > num_vars)
      num_vars = first_var_position;
    if(second_var_position > num_vars)
      num_vars = second_var_position;
    bounds[temp.getUtvpiPosition()] = std::min(bounds[temp.getUtvpiPosition()], bound);
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

OctagonsInterpolant::~OctagonsInterpolant(){}

void OctagonsInterpolant::updatePositions(Octagon & f){
  char first_sign = f.getFirstSign(), second_sign = f.getSecondSign();
  int first_var_position = f.getFirstVarPosition(), second_var_position = f.getSecondVarPosition();
  int f_position = f.getUtvpiPosition();

  // Only perform the update operation if
  // the octagon is not of the form 0 <= a (i.e. with position different from 0)
  std::cout << "Inside updatePosition " << f << std::endl;
  std::cout << first_sign << " " << first_var_position << " " << second_sign << " " << second_var_position << std::endl;
  std::cout << f_position << std::endl;
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

void OctagonsInterpolant::operate(int var_to_elim, Octagon & x, Octagon & y){
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
    std::cout << "Case +/- x (...); -/+ x (...)" << std::endl;
    // Case +/- x +/- y <= b1; -/+ x +/- y <= b2
    // FIX: Hmm consider the case +/- x +/- (-1) <= b1; -/+ x +/- (-1) <= b2
    // i.e. +/- x <= b1; -/+ x <= b2 according to the encoding
    if(second_sign_x == second_sign_y && second_var_position_x == second_var_position_y){
      Octagon temp(second_sign_x, '+', second_var_position_x, -1);
      bounds[temp.getUtvpiPosition()] = std::min(bounds[temp.getUtvpiPosition()], (bound_x + bound_y)/2);
      updatePositions(temp);
      std::cout << "haha" << std::endl;
#if PRINT_MSG
      printMessage(x, y, temp);
#endif

    }
    // Case +/- x +/- y <= b1; -/+ x -/+ y <= b2
    else if(second_sign_x != second_sign_y && second_var_position_x == second_var_position_y){
      // Do nothing!
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
      bounds[temp.getUtvpiPosition()] = std::min(bounds[temp.getUtvpiPosition()], bound_x + bound_y);
      updatePositions(temp);
#if PRINT_MSG
      printMessage(x, y, temp);
#endif
    }
  }
  
  // Case +/- x (...); (..) -/+ x (..)
  else if(first_var_position_x == second_var_position_y && first_var_position_x == var_to_elim){
    std::cout << "// Case +/- x (...); (..) -/+ x (..)" << std::endl;
    // Case +/- x +/- y <= b1; +/- y -/+ x <= b2
    if(second_sign_x == first_sign_y && second_var_position_x == first_var_position_y){
      Octagon temp(second_sign_x, '+', second_var_position_x, -1);
      bounds[temp.getUtvpiPosition()] = std::min(bounds[temp.getUtvpiPosition()], (bound_x + bound_y)/2);
      updatePositions(temp);
#if PRINT_MSG
      printMessage(x, y, temp);
#endif
    }
    // Case +/- x +/- y <= b1; -/+ y -/+ x <= b2
    else if(second_sign_x != first_sign_y && second_var_position_x == first_var_position_y){
      // Do nothing!
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
      bounds[temp.getUtvpiPosition()] = std::min(bounds[temp.getUtvpiPosition()], bound_x + bound_y);
      updatePositions(temp);
#if PRINT_MSG
      printMessage(x, y, temp);
#endif
    }
  }
  
  // Case (..) +/- x (..); -/+ x (...)
  else if(second_var_position_x == first_var_position_y && second_var_position_x == var_to_elim){
    std::cout << "// Case (..) +/- x (..); -/+ x (...)" << std::endl;
    // Case +/- y +/- x <= b1; -/+ x +/- y <= b2
    if(first_sign_x == second_sign_y && first_var_position_x == second_var_position_y){
      Octagon temp(first_sign_x, '+', first_var_position_x, -1);
      bounds[temp.getUtvpiPosition()] = std::min(bounds[temp.getUtvpiPosition()], (bound_x + bound_y)/2);
      updatePositions(temp);
#if PRINT_MSG
      printMessage(x, y, temp);
#endif
    }
    // Case +/- y +/- x <= b1; -/+ x -/+ y <= b2
    else if(first_sign_x != second_sign_y && first_var_position_x == second_var_position_y){
      // Do nothing!
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
      bounds[temp.getUtvpiPosition()] = std::min(bounds[temp.getUtvpiPosition()], bound_x + bound_y);
      updatePositions(temp);
#if PRINT_MSG
      printMessage(x, y, temp);
#endif
    }
  }
  
  // Case (..) +/- x (..); (..) -/+ x (..)
  else if(second_var_position_x == second_var_position_y && second_var_position_x == var_to_elim){
    std::cout << "// Case (..) +/- x (..); (..) -/+ x (..)" << std::endl;
    // Case +/- y +/- x <= b1; +/- y -/+ x <= b2
    if(first_sign_x == first_sign_y && first_var_position_x == first_var_position_y){
      Octagon temp(first_sign_x, '+', first_var_position_x, -1);
      bounds[temp.getUtvpiPosition()] = std::min(bounds[temp.getUtvpiPosition()], (bound_x + bound_y)/2);
      updatePositions(temp);
#if PRINT_MSG
      printMessage(x, y, temp);
#endif
    }
    // Case +/- y +/- x <= b1; -/+ y -/+ x <= b2
    else if(first_sign_x != first_sign_y && first_var_position_x == first_var_position_y){
      // Do nothing!
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
      bounds[temp.getUtvpiPosition()] = std::min(bounds[temp.getUtvpiPosition()], bound_x + bound_y);
      updatePositions(temp);
#if PRINT_MSG
      printMessage(x, y, temp);
#endif
    }
  }
}

void OctagonsInterpolant::buildInterpolat(){
      
#if DEBUG_OCT_INTER_
  int max_num_ineqs = 2*(num_vars+1)*(num_vars+1);
  std::cout << "Initial Inequalities:" << std::endl;
  for(int i = 0; i < max_num_ineqs; ++i)
    if(bounds[i] != INF){
      Octagon temp = Octagon(i);
      std::cout << temp;
      std::cout << " <= " << bounds[i] << std::endl;
    }
  std::cout << std::endl;
#endif
      
  // ----------------------------------------------------------------------------------------------------------------
  // Interpolation Algorithm
  for(auto it : variables_to_eliminate){
#if DEBUG_OCT_INTER_
    std::cout << "Eliminating variable x_" << it << "\n";
#endif
    
    for(auto x : positive_var_positions[it])
      for(auto y : negative_var_positions[it]){
	std::cout << x << " " << y << " " << it << std::endl;
	if(bounds[x] != INF && bounds[y] != INF){
	  Octagon first_octagon = Octagon(x);
	  Octagon second_octagon = Octagon(y);
	  std::cout << "first octagon " << first_octagon << std::endl;
	  std::cout << "second octagon " << second_octagon << std::endl;
	  operate(it, first_octagon, second_octagon);
	}
      }

    for(auto x : positive_var_positions[it])
      bounds[x] = INF;
    
    for(auto x : negative_var_positions[it])
      bounds[x] = INF;

#if DEBUG_OCT_INTER_
    std::cout << "After Eliminating Variable x_" << it << "\n";
    for(int i = 0; i < max_num_ineqs; ++i)
      if(bounds[i] != INF){
	Octagon temp = Octagon(i);
	std::cout << temp;
	std::cout << " <= " << bounds[i] << "\n";
      }
#endif
  }
  // ----------------------------------------------------------------------------------------------------------------
}
