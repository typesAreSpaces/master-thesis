#ifndef _PURIFIER_
#define _PURIFIER_

#include <iostream>
#include <z3++.h>
#include <string>
#include <map>

class Purifier{

  z3::context &                ctx;
  z3::expr &                   formula;
  z3::expr_vector              from;
  z3::expr_vector              to;
  z3::expr                     euf_component;
  z3::expr                     octagon_component;
  std::map<unsigned, unsigned> map_oct;
  std::map<unsigned, unsigned> map_euf;
  static unsigned              fresh_var_id;


  void     purify();
  z3::expr purifyEUFTerm(z3::expr &);
  z3::expr purifyOctagonTerm(z3::expr &);
  void     split(z3::expr &);
  
public:
  Purifier(z3::expr &);
  ~Purifier();

  z3::expr getEUF();
  z3::expr getOctagon();
  void     traverse(z3::expr &);
  
  friend std::ostream & operator << (std::ostream &, Purifier &);
};

#endif
