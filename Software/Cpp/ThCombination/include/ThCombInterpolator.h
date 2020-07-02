#ifndef _THCOMB_
#define _THCOMB_
#define _DEBUG_TH_COMB_ 0

#include "Purifier.h"
#include "DisjEqsPropagator.h"
#include "CDCL_T.h"
#include "ProofFactory.h"
#include <set>


class ThCombInterpolator {

  struct z3_const_comparator {
    bool operator() (z3::expr const & e1, z3::expr const & e2);
  };
  typedef std::set<z3::expr, z3_const_comparator> z3_expr_set;

  z3::context & ctx;

  Purifier      part_a;
  Purifier      part_b;

  z3::solver    euf_solver;
  z3::solver    oct_solver;

  z3::expr_vector shared_variables;
  z3::expr_map    partial_interpolants;

  void sharedVariables(Purifier const &, Purifier const &);
  void collectVariables(z3::expr const &, z3_expr_set &);

  void checkImpliedEqualities(z3::expr_vector &, z3::solver &);
  bool isProvable(z3::solver &, z3::expr const &);     // Perhaps this wont be used that much (??)
  void addConjunction(z3::solver &, z3::expr const &); // Perhaps this wont be used that much (?)

  z3::expr partialInterpolantConvex();// TODO: implement
  z3::expr partialInterpolantConflictClause();// TODO: implement
  z3::expr partialInterpolantUnitResolution(z3::expr const &, z3::expr const &);// TODO: implement
  
  void printf___(z3::expr const &);

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
