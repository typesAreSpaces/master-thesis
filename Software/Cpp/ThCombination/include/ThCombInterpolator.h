#ifndef _THCOMB_
#define _THCOMB_

#include "Purifier.h"

class ThCombInterpolator {
  z3::context & ctx;
  Purifier   part_a;
  Purifier   part_b;
  z3::solver euf_solver;
  z3::solver oct_solver;

  bool isProvable(z3::solver &, z3::expr const &);
  void addConjunction(z3::solver &, z3::expr const &);
  
  void printf___(z3::expr const &);
  void traverseProof1(z3::expr const &);
  void traverseProof2(z3::expr const &, z3::expr_vector &);
  
public:
  ThCombInterpolator(z3::context &, z3::expr const &, z3::expr const &);
  ~ThCombInterpolator();

  void getInterpolant();
  
  friend std::ostream & operator << (std::ostream &, ThCombInterpolator &);
};

#endif
