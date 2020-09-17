#ifndef _OCT_TERM_
#define _OCT_TERM_
#define _DEBUG_OCT_TERM_ 0

#include <z3++.h>

class OctagonTerm : public z3::expr {

  void update(z3::expr const &);
  void octagonize();
  void onlyLEQ();

  z3::expr multiplyByNegativeOne(z3::expr const &);

  public:
  OctagonTerm(z3::expr const &, bool);
  z3::expr toZ3() const;
};


#endif
