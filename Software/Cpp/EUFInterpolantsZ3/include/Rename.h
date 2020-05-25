#ifndef _RENAME_
#define _RENAME_

#include <string>
#include <z3++.h>
#include <set>
#include <vector>
#include <utility>

void traversePartA(z3::expr const &, std::vector<bool> &, std::set<std::string> &);
void traversePartB(z3::expr const &, std::vector<bool> &, std::set<std::string> &, std::set<std::string> &);

z3::expr reformulate(z3::expr const &, std::set<std::string> const &, std::set<std::string> const &);
z3::expr reformulate(z3::expr const &, std::set<std::string> const &);

z3::expr rename(z3::expr const &, z3::expr const &);
z3::expr rename(z3::expr const &, std::set<std::string> const &);

z3::expr_vector rename(z3::expr_vector const &, z3::expr_vector const &);
z3::expr_vector rename(z3::expr_vector const &, std::set<std::string> const &);

#endif
