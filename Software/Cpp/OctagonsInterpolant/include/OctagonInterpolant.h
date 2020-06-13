#ifndef _OCT_INTERP_
#define _OCT_INTERP_
#define _DEBUG_ELIM_ 0

#include "OctagonParser.h"

class OctagonInterpolant : public OctagonParser {

  z3::expr_vector result;
  void elimination(UtvpiPosition, UtvpiPosition, VarValue);

  public:
  OctagonInterpolant(z3::expr_vector const &);
  void buildInterpolant();
  z3::expr_vector getInterpolant() const;
};

#endif
