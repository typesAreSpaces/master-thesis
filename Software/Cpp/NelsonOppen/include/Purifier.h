#ifndef _PURIFIER_
#define _PURIFIER_

#include <iostream>
#include <z3++.h>
#include <string>
#include <map>
#include <vector>

class Purifier{

  z3::context &                ctx;
  z3::expr &                   formula;

  std::map<unsigned, unsigned> map_oct;
  std::map<unsigned, unsigned> map_euf;
  
  z3::expr_vector              from;
  z3::expr_vector              to;
  
  z3::expr_vector              euf_component;
  z3::expr_vector              octagon_component;
  
  static unsigned              fresh_var_id;
  std::vector<bool>            visited;

  void     purify();
  void     traverse(z3::expr &);
  z3::expr purifyEUFTerm(z3::expr &);
  z3::expr purifyOctagonTerm(z3::expr &);
  void     split(z3::expr const &);
  bool     earlyExit(z3::expr const &);
  
public:
  Purifier(z3::expr &);
  ~Purifier();
  
  friend std::ostream & operator << (std::ostream &, Purifier &);
};

#endif
