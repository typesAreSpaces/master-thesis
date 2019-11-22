#ifndef _PURIFIER_
#define _PURIFIER_
#define DEBUG_PUR true

#include <vector>
#include <string>
#include <z3++.h>

class Purifier{
private:
  z3::expr euf_formula;
  z3::expr octagon_formula;
public:
  Purifier(const z3::expr &, const std::vector<std::string> &);
  ~Purifier();
  z3::expr getEUFFormula();
  z3::expr getOctagonFormula();
};
