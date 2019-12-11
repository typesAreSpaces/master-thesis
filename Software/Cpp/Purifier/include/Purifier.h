#include <iostream>
#include <z3++.h>
#include <string>
#include <set>

class Purifier{

  z3::context & ctx;
  z3::expr & formula;
  z3::expr_vector from;
  z3::expr_vector to;
  std::set<unsigned> id_terms_seen;
  
  z3::expr purifyEUFTerm(z3::expr &);
  z3::expr purifyOctagonTerm(z3::expr &);
  void traverse(z3::expr &);
  
public:
  Purifier(z3::expr &);
  ~Purifier();
  z3::expr purify();
  friend std::ostream & operator << (std::ostream &, Purifier &);
};
