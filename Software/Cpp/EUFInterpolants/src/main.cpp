#include <iostream>
#include <fstream>
#include <cstdlib>
#include <ctime>

#include "CongruenceClosure.h"
#include "EUFInterpolant.h"
#include "HornClauses.h"

int main(int argc, char ** argv){
  
  std::string file = "./tests/smt2lib_2/kapurEUFExample.smt2";
  //std::string file = "/Users/joseabelcastellanosjoo/Documents/QF_UF/2018-Goel-hwbench/QF_UF_firewire_tree.5.prop3_ab_reg_max.smt2";
  //std::string file = "/Users/joseabelcastellanosjoo/Documents/QF_UF/2018-Goel-hwbench/QF_UF_firewire_tree.3.prop2_ab_reg_max.smt2";
  //std::string file = "/Users/joseabelcastellanosjoo/Documents/QF_UF/2018-Goel-hwbench/QF_UF_needham.3.prop4_ab_reg_max.smt2";

  z3::config cfg;
  cfg.set("PROOF", true);
  cfg.set("MODEL", true);
  cfg.set("TRACE", false);
  z3::context ctx(cfg);
  Z3_ast inputFormula = Z3_parse_smtlib2_file(ctx, file.c_str(), 0, 0, 0, 0, 0, 0);
  std::set<std::string> symbolsToElim = {"v"};

  /*
  CongruenceClosure cc(ctx, inputFormula, symbolsToElim);
  UnionFind & uf = cc.getEC();
  
  HornClauses hC;
  hC.addHornClause(uf, cc.getTerm(9), cc.getTerm(13));
  hC.addHornClause(uf, cc.getTerm(17), cc.getTerm(19));

  //std::cout << hC << std::endl;
  */

  EUFInterpolant eufI (ctx, inputFormula, symbolsToElim);
  
  return 0;
}
