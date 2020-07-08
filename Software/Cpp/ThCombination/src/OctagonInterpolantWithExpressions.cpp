#include "OctagonInterpolantWithExpressions.h"

OctagonInterpolantWithExpressions::OctagonInterpolantWithExpressions(z3::expr_vector const & input_a, z3::expr_vector const & input_b) :
  RenameWithExpressions(input_a, input_b), OctagonInterpolant(renamed_input_a)
{
}
