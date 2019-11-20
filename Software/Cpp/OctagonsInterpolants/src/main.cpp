#include "OctagonsInterpolant.h"
#include <map>

// int main(){

//   Octagon temp1('+', '+', 2, 3);
//   temp1.normalize(1);
//   std::cout << temp1.getUtvpiPosition() << std::endl;
//   Octagon temp1_ = Octagon(temp1.getUtvpiPosition());

//   Octagon temp2('+', '-', 2, 3);
//   temp2.normalize(1);
//   Octagon temp2_ = Octagon(temp2.getUtvpiPosition());

//   Octagon temp3('-', '+', 2, 3);
//   temp3.normalize(1);
//   Octagon temp3_ = Octagon(temp3.getUtvpiPosition());

//   Octagon temp4('-', '-', 2, 3);
//   temp4.normalize(1);
//   Octagon temp4_ = Octagon(temp4.getUtvpiPosition());
  
//   Octagon temp5('-', '+', 2, -1);
//   temp5.normalize(1);
//   Octagon temp5_ = Octagon(temp5.getUtvpiPosition());

//   std::cout << temp1 << std::endl;
//   std::cout << temp1_ << std::endl;

//   std::cout << temp2 << std::endl;
//   std::cout << temp2_ << std::endl;

//   std::cout << temp3 << std::endl;
//   std::cout << temp3_ << std::endl;

//   std::cout << temp4 << std::endl;
//   std::cout << temp4_ << std::endl;

//   std::cout << temp5 << std::endl;
//   std::cout << temp5_ << std::endl;

//   for(int i = 0; i < 10; ++i){
//     Octagon temp(i);
//     std::cout << temp << std::endl;
//   }
    
//   return 0;
// }

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
    try{
      z3::context ctx;
      auto input_formula = z3::mk_and(ctx.parse_file(argv[1])).simplify();
      std::cout << input_formula << std::endl;
	
      std::set<std::string> symbols_to_elim;
      for(int index = 2; index < argc; ++index){
	symbols_to_elim.insert(argv[index]);
      }
      
      OctagonsInterpolant oct(input_formula, symbols_to_elim);
      oct.buildInterpolant();
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
