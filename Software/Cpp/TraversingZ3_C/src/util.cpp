/*++
  Copyright (c) 2015 Microsoft Corporation

  --*/

#include "util.h"

enum option {EXIT_, INTERPOLANT_, PROVE_};
const bool debug = false;

std::istream& operator>>(std::istream& is, option& i){
  int temp;
  if (is >> temp)
    i = static_cast<option>(temp);
  return is;
}

void interface(){
  option input;
  std::string file;

  do{
    std::cout << "Menu:" << std::endl;
    std::cout << "1. Interpolant" << std::endl;
    std::cout << "2. Prove" << std::endl;
    std::cout << "0. Exit" << std::endl;
    std::cin >> input;
    switch(input){
    case INTERPOLANT_:
      std::cout << "Name of the file: ";
      std::cin >> file;
      try{
	if(debug)
	  interpolantFromFile("./Testing/" + file);
	else
	  interpolantFromFile(file);
      }
      catch(z3::exception & ex){
	std::cout << "unexpected error: " << ex << "\n";
      }
      break;
    case PROVE_:
      std::cout << "Name of the file: ";
      std::cin >> file;
      try{
	if(debug)
	  proveFromFile("./Testing/" + file);
	else
	  proveFromFile(file);
      }
      catch(z3::exception & ex){
	std::cout << "unexpected error: " << ex << "\n";
      }
      break;
    case EXIT_:
      break;
    }
  }
  while(input != EXIT_);
}

void testSMT2(int argc, char ** argv){
  std::cout << "Number of files: " << argc << std::endl;
  if(argc >= 2){  
    for(int i = 2; i < argc; ++i)
      proveFromFile(argv[i]);
  }
  else
    std::cout << "Expecting only one file!" << std::endl;
}

void proveFromFile(std::string file){
  std::cout << "Proving from file: " << file << std::endl;

  z3::config cfg;
  cfg.set("PROOF", true);
  cfg.set("MODEL", true);
  cfg.set("TRACE", true);
  z3::context ctx(cfg);
  Z3_ast inputFormula = Z3_parse_smtlib2_file(ctx, (Z3_string)file.c_str(), 0, 0, 0, 0, 0, 0);
  z3::expr _inputFormula(ctx, inputFormula);
  
  z3::solver s(ctx);
  s.add(!_inputFormula);
  if (s.check() == z3::unsat) 
    std::cout << "proved" << "\n";
  else {
    std::cout << "failed to prove" << "\n";
    z3::model m = s.get_model();
    std::cout << "counterexample:\n" << m << "\n";
  }
}

void interpolantFromFile(std::string file){
  std::cout << "Compute Interpolant from file: " << file << std::endl;

  z3::config cfg;
  cfg.set("PROOF", true);
  cfg.set("MODEL", true);
  cfg.set("TRACE", true);
  z3::context ctx(cfg);
  Z3_ast inputFormula = Z3_parse_smtlib2_file(ctx, (Z3_string)file.c_str(), 0, 0, 0, 0, 0, 0);
  z3::expr _inputFormula(ctx, inputFormula);

  z3::params param_(ctx);
  Z3_ast_vector * vector = new Z3_ast_vector();
  Z3_model * model = new Z3_model();
  Z3_lbool result = Z3_compute_interpolant(ctx, _inputFormula, param_, vector, model);
  if (result == Z3_L_TRUE) {
    std::cout << "true" << std::endl;
  } else if (result == Z3_L_FALSE) {
    std::cout << "false" << std::endl;
    std::cout << z3::ast_vector(ctx, *vector) << std::endl;
  } else {
    std::cout << "unknown" << std::endl;
  }
}
