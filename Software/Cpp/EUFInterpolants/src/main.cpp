#include <iostream>
#include <fstream>
#include <cstdlib>
#include <ctime>

#include "CongruenceClosure.h"
#include "EUFInterpolant.h"
#include "HornClauses.h"
#include "z3++.h"
#include "CircularList.h"

int main(int argc, char ** argv){

	// Testing "CircularList.h"

	CircularList<unsigned int> a;
	a.add(10), a.add(20), a.add(12);
	CircularList<unsigned int> b;
	b.add(13), b.add(14), b.add(15);
	a.merge(&b);
	a.print(std::cout);
	b.print(std::cout);
	a.merge(&b);
	a.print(std::cout);
	b.print(std::cout);
	
  
  // std::string file = "./tests/smt2lib_2/kapurEUFExample2_2.smt2";
  // //std::string file = "/Users/joseabelcastellanosjoo/Documents/QF_UF/2018-Goel-hwbench/QF_UF_firewire_tree.5.prop3_ab_reg_max.smt2";
  // //std::string file = "/Users/joseabelcastellanosjoo/Documents/QF_UF/2018-Goel-hwbench/QF_UF_firewire_tree.3.prop2_ab_reg_max.smt2";
  // //std::string file = "/Users/joseabelcastellanosjoo/Documents/QF_UF/2018-Goel-hwbench/QF_UF_needham.3.prop4_ab_reg_max.smt2";

  // z3::config cfg;
  // cfg.set("PROOF", true);
  // cfg.set("MODEL", true);
  // cfg.set("TRACE", false);
  // z3::context ctx(cfg);
  // Z3_ast inputFormula = Z3_ast_vector_get(ctx, Z3_parse_smtlib2_file(ctx, file.c_str(), 0, 0, 0, 0, 0, 0), 0);
  // std::set<std::string> symbolsToElim = {"f"};

  // EUFInterpolant eufI (ctx, inputFormula, symbolsToElim);
  // eufI.algorithm();

	
	
  return 0;
}
