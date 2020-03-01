#include "CongruenceClosure.h"

CongruenceClosure::CongruenceClosure(const unsigned & min_id, const z3::expr_vector & subterms, CCList & cc_list, UnionFind & uf) :
  min_id(min_id), subterms(subterms), cc_list(cc_list),
  uf(uf), sig_table(uf){
}

CongruenceClosure::~CongruenceClosure(){
#if DEBUG_DESTRUCTORS_CC
  std::cout << "Done ~CongruenceClosure" << std::endl;
#endif
}

std::ostream & operator << (std::ostream & os, const CongruenceClosure & cc){
  return os;
}
