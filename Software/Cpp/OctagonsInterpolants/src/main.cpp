#include "OctagonsInterpolant.h"

std::set<unsigned> getSymbols(const z3::expr &);
void auxiliarGetSymbols(const z3::expr &, std::set<unsigned> &);

std::set<unsigned> getSymbols(const z3::expr & formula){
  std::set<unsigned> symbols;
  auxiliarGetSymbols(formula, symbols);
  return symbols;
}

void auxiliarGetSymbols(const z3::expr & e, std::set<unsigned> & symbols){
  // std::cout << "Formula " << e << std::endl;
  // std::cout << "Name " << e.decl().name().str() << std::endl;
  if (e.is_app()) {
    unsigned num = e.num_args();
    if(num == 0)
      symbols.insert(e.id());
    for (unsigned i = 0; i < num; ++i)
      auxiliarGetSymbols(e.arg(i), symbols);
  }
  else if (e.is_quantifier()) {
  }
  else {
    assert(e.is_var());
  }
}

// int main(int argc, char ** argv){
//   if(argc == 2){
//     std::ifstream file;
//     file.open(argv[1], std::ifstream::in);

//     std::cout << argv[1] << std::endl;

//     OctagonsInterpolant oc = OctagonsInterpolant(file);
//     oc.buildInterpolant();
//   }
//   return 0;
// }

int main(int argc, char ** argv){
  
  if(argc >= 2) {
    try {
      z3::context ctx;
      auto input_formula = z3::mk_and(ctx.parse_file(argv[1])).simplify();
      std::cout << input_formula << std::endl;
      std::cout << input_formula.num_args() << std::endl;

      for(unsigned utvpi_index = 0; utvpi_index < input_formula.num_args(); ++utvpi_index){
	std::cout << input_formula.arg(utvpi_index) << std::endl;
      }

      for(auto x : getSymbols(input_formula)){
	std::cout << x << std::endl;
      }
      
      std::set<std::string> symbols_to_elim;
    
      for(int index = 2; index < argc; ++index)
	symbols_to_elim.insert(argv[index]);
      
      // EUFInterpolant euf(input_formula, symbols_to_elim, aux_expr.decl().range());
      // auto result = euf.buildInterpolant();
      
      // std::cout << "Input formula is : " << std::endl << input_formula << std::endl;
      // std::cout << "Symbols to eliminate: " << std::endl;
      // for(auto symbol_name : symbols_to_elim)
      // 	std::cout << symbol_name << " ";
      // std::cout << std::endl;
      // std::cout << "The interpolant is: " << std::endl << result.simplify() << std::endl;
      // std::cout << "The interpolant is: " << std::endl << result << std::endl;

      // // Test if the output is an interpolant
      // z3::solver s(ctx);
      // s.add(!z3::implies(input_formula, result));
      // switch(s.check()){
      // case z3::unsat:
      //   std::cout << "unsat" << std::endl;
      //   break;
      // case z3::sat:
      //   std::cout << "sat" << std::endl;
      //   break;
      // case z3::unknown:
      //   std::cout << "unknown" << std::endl;
      //   break;
      // }
    }
    catch(...){
      std::cout << "File not found" << std::endl;
    }
  }
  else
    std::cout << "Not enough arguments" << std::endl;
  return 0;
}
