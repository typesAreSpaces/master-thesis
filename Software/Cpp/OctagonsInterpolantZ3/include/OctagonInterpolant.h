#ifndef _OCT_INTERP_
#define _OCT_INTERP_

#include "OctagonParser.h"

class OctagonInterpolant : public OctagonParser {

  z3::expr_vector result;
  void propagate(UtvpiPosition, UtvpiPosition);

  public:
  OctagonInterpolant(z3::expr_vector const &);
  void buildInterpolant();
  z3::expr_vector getInterpolant() const;
};

#endif
