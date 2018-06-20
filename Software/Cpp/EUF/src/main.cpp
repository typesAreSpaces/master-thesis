#include <iostream>
#include <fstream>
#include <utility>
#include "unionfind.hpp"
#include "terms.hpp"
#include "formulas.hpp"

int main(int argc, char ** argv){

  /*
  UnionFind uf(20);
  uf._union(1, 2);
  uf._union(2, 3);
  uf._union(3, 4);
  std::cout << (uf._findSet(1) == uf._findSet(4)) << std::endl;
  std::cout << (uf._findSet(1) == uf._findSet(5)) << std::endl;
  */

  Constant * c1 = new Constant("c1");
  Constant * c2 = new Constant("c2");
  Function * f1 = new Function("f");
  f1->addArg(c1);
  f1->addArg(c2);
  Function * f2 = new Function("f");
  f2->addArg(f1);
  f2->addArg(c2);
  Function * f3 = new Function("f");
  f3->addArg(f2);
  f3->addArg(c2);

  Function * g1 = new Function("g");
  g1->addArg(f1);
  g1->addArg(c2);
  Function * f4 = new Function("f");
  f4->addArg(g1);
  f4->addArg(c2);
  
  std::cout << *f3 << std::endl;
  std::cout << *f4 << std::endl;
  
  //g->addArg(g); hahaha, don't do this!

  Eq * eq1 = new Eq("eq1", f4, c1, true);
  
  return 0;
}
