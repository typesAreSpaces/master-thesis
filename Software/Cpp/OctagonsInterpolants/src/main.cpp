#include <iostream>
#include "OctagonsInterpolant.h"
#include <z3++.h>
#include <set>

// int main(int argc, char ** argv){
//   if(argc == 2){
//     std::ifstream file;
//     file.open(argv[1], std::ifstream::in);

//     Octagons oc = Octagons(file);
//     oc.interpolation(std::cout);
//   }
//   return 0;
// }


int main(int argc, char ** argv){
  
  if(argc >= 2) {
    try {
      z3::context ctx;
      auto input_formula = z3::mk_and(ctx.parse_file(argv[1]));
      std::cout << input_formula << std::endl;
      
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
