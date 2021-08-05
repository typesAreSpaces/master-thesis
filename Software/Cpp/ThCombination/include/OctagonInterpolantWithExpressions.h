#ifndef _OCT_INTERP_WE_
#define _OCT_INTERP_WE_

#include "Rename.h"
#include "OctagonInterpolant.h"

class OctagonInterpolantWithExpressions : public RenameWithExpressions, public OctagonInterpolant {
  public:
    OctagonInterpolantWithExpressions(z3::expr_vector const &, z3::expr_vector const &);

    friend std::ostream & operator << (std::ostream &, OctagonInterpolantWithExpressions const &);
};

#endif
