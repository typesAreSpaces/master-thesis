#include "ThCombInterpolatorWithExpressions.h"

ThCombInterpolatorWithExpressions::ThCombInterpolatorWithExpressions(z3::expr_vector const & input_a, z3::expr_vector const & input_b) :
  RenameWithExpressions(input_a, input_b), ThCombInterpolator(renamed_input_a, renamed_input_b)
{
}

std::ostream & operator << (std::ostream & os, ThCombInterpolatorWithExpressions const & p) {
  return os << "The interpolant is: " << p.computed_interpolant;
}

