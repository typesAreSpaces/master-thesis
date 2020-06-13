#ifndef _PURIFIER_
#define _PURIFIER_

#include <iostream>
#include <z3++.h>
#include <string>
#include <map>
#include <vector>

// Accepts a *conjunction* of literals
// in QF_UFLIA

class Purifier {

protected:
  static unsigned fresh_var_id;

  z3::context &   ctx;
  
  z3::expr_vector oct_component;
  z3::expr_vector euf_component;

  std::map<unsigned, unsigned> map_oct;
  std::map<unsigned, unsigned> map_euf;

  z3::expr_vector from;
  z3::expr_vector to;
  z3::expr const  formula;

private:  
  z3::expr purify(z3::expr const &);
  z3::expr traverse(z3::expr const &);
  z3::expr purifyOctagonTerm(z3::expr const &);
  z3::expr purifyEUFTerm(z3::expr const &);

  void split(z3::expr const &);
  
public:
  Purifier(z3::expr const &);

  void addEufFormulasToSolver(z3::solver &);
  void addOctFormulasToSolver(z3::solver &);
  bool inside(z3::expr const &);
  
  friend std::ostream & operator << (std::ostream &, Purifier &);
};

#endif
