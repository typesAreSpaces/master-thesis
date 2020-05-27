#ifndef _EUF_INTERPOLANT_
#define _EUF_INTERPOLANT_
#define DEBUG_DESTRUCTOR_EUF 0
#define DEBUG_EUFINTERPOLANT 0
#define DEBUG_EXPOSE_UNCOMMS 1
#define DEBUG_COND_ELIM      1

#include "Input.h"

class EUFInterpolant : public Input {

  z3::expr_vector buildHCBody(z3::expr const &, z3::expr const &);
  void            exposeUncommons();
  void            conditionalElimination(); // TODO: Implement this
  
 public:
  EUFInterpolant(z3::expr_vector const &);
  ~EUFInterpolant();
  z3::expr              buildInterpolant(std::vector<Replacement>);  // TODO:
  friend std::ostream & operator << (std::ostream &, EUFInterpolant &);
};

#endif
