#include "OctagonParser.h"

OctagonParser::OctagonParser(z3::expr_vector const & assertions) : 
  ctx(assertions.ctx()), z3_variables(ctx),
  id_table(), checked_ids(), bounds() // FIX: Wrong arity
{
  // KEEP: working here
  for(auto const & assertion : assertions){
    auto const & inequality = assertion.arg(0);
    auto const & bound = assertion.arg(1);
    std::cout << "Inequality: " << inequality << std::endl;
    auto const & f = inequality.decl();
    std::cout << "Declaration: " << f << std::endl;
    for(unsigned _arg_index = 0; _arg_index < inequality.num_args(); _arg_index++){
      auto const & _f = inequality.arg(_arg_index).decl();
      std::cout << "Declaration: " << _f << std::endl;
      std::cout << _arg_index << "-th var: " << inequality.arg(_arg_index) << std::endl;

    }

    std::cout << "Bound (usign): " << bound.get_numeral_int() << std::endl;

  }
  // REMAINDER: id_table, checked_ids, bounds are still undefined
}
