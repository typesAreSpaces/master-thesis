#ifndef _RENAME_
#define _RENAME_

#include <iostream>
#include <string>
#include <z3++.h>
#include <set>
#include <vector>

class Rename {

  z3::expr const & part_a;
  z3::expr const & part_b;
  std::set<std::string> a_local_names;
  std::set<std::string> common_names;
  std::vector<bool> visited;

  void     traversePartA(z3::expr const &);
  void     traversePartB(z3::expr const &);
  z3::expr reformulate(z3::expr const &);
  
public:
  Rename(z3::expr const &, z3::expr const &);
  ~Rename();
};

#endif
