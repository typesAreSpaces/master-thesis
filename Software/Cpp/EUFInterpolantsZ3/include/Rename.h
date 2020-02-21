#ifndef _RENAME_
#define _RENAME_

#include <string>
#include <z3++.h>
#include <set>
#include <vector>

void     traversePartA(z3::expr const &, std::vector<bool> &, std::set<std::string> &);
void     traversePartB(z3::expr const &, std::vector<bool> &, std::set<std::string> &, std::set<std::string> &);
z3::expr reformulate(z3::expr const &, const std::set<std::string> &, const std::set<std::string> &);
z3::expr reformulate(z3::expr const &, const std::set<std::string> &);
void     rename(z3::expr &, z3::expr &);
void     rename(z3::expr &, const std::set<std::string> &);

#endif
