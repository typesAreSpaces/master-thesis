#ifndef _REPLACEMENT_
#define _REPLACEMENT_

struct Replacement {
  unsigned clause1, clause2;
  Replacement(unsigned clause1, unsigned clause2) :
    clause1(clause1), clause2(clause2){}
  friend std::ostream & operator << (std::ostream & os, const Replacement & r){
    os << "Merge " << r.clause1 << " with " << r.clause2;
    return os;
  }
};

#endif
