#ifndef _THCOMB_
#define _THCOMB_
#define _DEBUG_TH_COMB_ 0

#include "Purifier.h"
#include "DisjEqsPropagator.h"
#include "CDCL_T.h"
#include "PicoSATProofFactory.h"
#include "EUFInterpolantWithExpressions.h"
#include "OctagonInterpolantWithExpressions.h"
#include <set>

class ThCombInterpolator {

  struct z3_const_comparator {
    bool operator() (z3::expr const & e1, z3::expr const & e2);
  };
  typedef std::set<z3::expr, z3_const_comparator> z3_expr_set;
   
  enum Theory {
    EUF, OCT
  };

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

  void partialInterpolantConvex(z3::expr const &, z3::expr_map &, Theory); // TODO: implement, signature can be modified as needed
  void partialInterpolantNonConvex(CDCL_T &, PicoProofFactory const &, z3::expr const &, unsigned, Theory);
  
public:
  ThCombInterpolator(z3::expr_vector const &, z3::expr_vector const &);
  ~ThCombInterpolator();

  void getInterpolant();
  
  friend std::ostream & operator << (std::ostream &, ThCombInterpolator &);
};

#endif
