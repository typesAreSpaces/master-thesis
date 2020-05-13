#include "CongruenceClosure.h"

CongruenceClosure::CongruenceClosure(const Z3Subterms & subterms,
				     UnionFindExplain & uf) :
  subterms(subterms), uf(uf), sig_table(uf)
{
}

CongruenceClosure::~CongruenceClosure(){
#if DEBUG_DESTRUCTORS_CC
  std::cout << "Done ~CongruenceClosure" << std::endl;
#endif
}

UnionFindExplain & CongruenceClosure::getUnionFindExplain() const {
  return uf;
}

std::ostream & operator << (std::ostream & os, const CongruenceClosure & cc){
  return os;
}
