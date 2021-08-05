#include "ThCombInterpolatorWithExpressions.h"

ThCombInterpolatorWithExpressions::ThCombInterpolatorWithExpressions(z3::expr_vector const & input_a, z3::expr_vector const & input_b) :
  RenameWithExpressions(input_a, input_b), ThCombInterpolator(renamed_input_a, renamed_input_b)
{
}

std::ostream & operator << (std::ostream & os, ThCombInterpolatorWithExpressions & p) {
  //os << "The interpolant is: ";
  try {
    os << p.removePrefix(p.computed_interpolant);
  }
  catch(char const * e){
    std::cerr << e << std::endl;
  }
  return os;
}

