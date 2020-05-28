#ifndef _EUF_INTERPOLANT_
#define _EUF_INTERPOLANT_
#define DEBUG_DESTRUCTOR_EUF 0
#define DEBUG_EUFINTERPOLANT 0
#define DEBUG_EXPOSE_UNCOMMS 0
#define DEBUG_COND_ELIM      0

#include "Input.h"
#include <set>

typedef unsigned Z3Index ;

class EUFInterpolant : public Input {

  z3::expr_vector const & assertions;
  Hornsat                 hsat;

  z3::expr_vector buildHCBody(z3::expr const &, z3::expr const &);
  void            exposeUncommons();
  void            conditionalElimination(); // TODO: Implement this
  z3::expr_vector commonReplacements(z3::expr const &);
  
 public:
  EUFInterpolant(z3::expr_vector const &);
  ~EUFInterpolant();

  z3::expr buildInterpolant();  // TODO: Implement this

  friend std::ostream & operator << (std::ostream &, EUFInterpolant &);
};

#endif
