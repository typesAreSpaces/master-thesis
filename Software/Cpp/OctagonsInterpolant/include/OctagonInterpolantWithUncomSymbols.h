#ifndef _OCT_INTERP_US_
#define _OCT_INTERP_US_

#include "Rename.h"
#include "OctagonInterpolant.h"

class OctagonInterpolantWithUncomSymbols: public RenameWithUncomSymbols, public OctagonInterpolant {
  public:
    OctagonInterpolantWithUncomSymbols(z3::expr_vector const &, std::set<std::string> const &);
};

#endif
