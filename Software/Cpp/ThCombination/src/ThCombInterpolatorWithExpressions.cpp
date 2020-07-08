#include "ThCombInterpolatorWithExpressions.h"

ThCombInterpolatorWithExpressions::ThCombInterpolatorWithExpressions(z3::expr_vector const & input_a, z3::expr_vector const & input_b) :
  RenameWithExpressions(input_a, input_b), ThCombInterpolator(renamed_input_a, renamed_input_b)
{
}
