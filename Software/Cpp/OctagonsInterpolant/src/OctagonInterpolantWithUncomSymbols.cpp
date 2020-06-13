#include "OctagonInterpolantWithUncomSymbols.h"

OctagonInterpolantWithUncomSymbols::OctagonInterpolantWithUncomSymbols(z3::expr_vector const & input_a, std::set<std::string> const & uncommon_symbols) :
  RenameWithUncomSymbols(input_a, uncommon_symbols), OctagonInterpolant(renamed_input)
{
}
