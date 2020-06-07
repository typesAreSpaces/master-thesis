#include "OctagonsInterpolant.h"
#include <map>

int main(int argc, char ** argv){
  
  if(argc >= 2) {
    try{
      z3::context ctx;
      auto input_formula = z3::mk_and(ctx.parse_file(argv[1])).simplify();
	
      std::vector<std::string> symbols_to_elim;
      for(int index = 2; index < argc; ++index)
	symbols_to_elim.push_back(argv[index]);
      
      OctagonsInterpolant oct(input_formula, symbols_to_elim);
      auto result = oct.buildInterpolant();

      std::cout << "Input formula: " << input_formula << std::endl;
      std::cout << "Interpolant: " << result << std::endl;

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
    catch(z3::exception & e){
      std::cout << "File not found " << std::endl;
      std::cout << e << std::endl;
    }
  }
  else
    std::cout << "Not enough arguments" << std::endl;
  
  return 0;
}
