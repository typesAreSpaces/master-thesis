#ifndef _OCT_INTERP_
#define _OCT_INTERP_
#define _DEBUG_ELIM_ 0

#include "OctagonParser.h"

class OctagonInterpolant : public OctagonParser {

  z3::expr_vector result;
  void elimination(UtvpiPosition, UtvpiPosition, VarValue);
  void updatePositions(Coeff const &, Var const &, VarValue const &, UtvpiPosition const &);

  protected:
  unsigned num_elims;

  public:
  OctagonInterpolant(z3::expr_vector const &);
  void buildInterpolant();
  z3::expr_vector getInterpolant() const;
};

#endif
