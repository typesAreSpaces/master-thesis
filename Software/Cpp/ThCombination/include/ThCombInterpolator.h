#ifndef _THCOMB_
#define _THCOMB_

#include "Purifier.h"

class ThCombInterpolator {
  z3::context & ctx;

  Purifier      part_a;
  Purifier      part_b;

  z3::solver    euf_solver;
  z3::solver    oct_solver;

  z3::expr_map  partial_interpolants;

  void checkImpliedEqualities(z3::expr_vector &, z3::solver &);
  bool isProvable(z3::solver &, z3::expr const &);     // Perhaps this wont be used that much (??)
  void addConjunction(z3::solver &, z3::expr const &); // Perhaps this wont be used that much (?)

  z3::expr partialInterpolantConvex();
  z3::expr partialInterpolantClauses();
  z3::expr partialInterpolantThLemmas();
  // The first argument is a partial interpolant
  // The second argument is a proof
  z3::expr partialInterpolantUnitResolution(z3::expr const &, z3::expr const &); // Here
  
  void printf___(z3::expr const &); // Here
  void traverseProof1(z3::expr const &); // Here
  void traverseProof2(z3::expr const &, z3::expr_vector &);
  
public:
  ThCombInterpolator(z3::context &, 
      z3::expr_vector const &, z3::expr_vector const &);
  ~ThCombInterpolator();

  void getInterpolant();
  
  friend std::ostream & operator << (std::ostream &, ThCombInterpolator &);
};

#endif
