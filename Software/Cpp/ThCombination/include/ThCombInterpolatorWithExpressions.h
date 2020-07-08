#ifndef _THCOMB_WE_
#define _THCOMB_WE_

#include "Rename.h"
#include "ThCombInterpolator.h"

class ThCombInterpolatorWithExpressions : public RenameWithExpressions, public ThCombInterpolator {
  public:
    ThCombInterpolatorWithExpressions(z3::expr_vector const &, z3::expr_vector const &);
};

#endif
