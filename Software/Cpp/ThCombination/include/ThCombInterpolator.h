#ifndef _THCOMB_
#define _THCOMB_
#define _DEBUG_TH_COMB_ 0
#define _MSG(x) std::cout << x
#define _SKIP do {} while(0)
#if 0
#define DEBUG_LOOP_MSG(x) _MSG(x)
#else
#define DEBUG_LOOP_MSG(x) _SKIP
#endif
#if 0
#define DEBUG_NON_CONV_MSG(x) _MSG(x)
#else
#define DEBUG_NON_CONV_MSG(x) _SKIP
#endif
#if 0
#define DEBUG_CONFLICT_MSG(x) _MSG(x)
#else
#define DEBUG_CONFLICT_MSG(x) _SKIP
#endif

#include "Purifier.h"
#include "OctagonTerm.h"
#include "DisjEqsPropagator.h"
#include "CDCL_T.h"
#include "PicoSATProofFactory.h"
#include "EUFInterpolant.h"
#include "OctagonInterpolant.h"
#include "Theories.h"
#include <set>

class ThCombInterpolator {

  struct z3_const_comparator {
    bool operator() (z3::expr const & e1, z3::expr const & e2);
  };
  typedef std::set<z3::expr, z3_const_comparator> z3_expr_set;

  z3::context & ctx;

  Purifier part_a;
  Purifier part_b;

  z3::expr_vector shared_variables;
  z3::expr_map    partial_interpolants;

  void sharedVariables(Purifier const &, Purifier const &);
  void collectVariables(z3::expr const &, z3_expr_set &);
  void checkImpliedEqualities(z3::expr_vector const &, z3::solver &);

  void partialInterpolantConflict(z3::expr const &, z3::expr_vector const &, 
      z3::expr_map &, Theory); 
  void partialInterpolantNonConvex(CDCL_T &, PicoProofFactory const &, 
      z3::expr const &, unsigned, Theory);

  protected:
  z3::expr computed_interpolant;

  public:
  ThCombInterpolator(z3::expr_vector const &, z3::expr_vector const &);
  ~ThCombInterpolator();

  void getInterpolant();

  friend std::ostream & operator << (std::ostream &, ThCombInterpolator &);
};

#endif
