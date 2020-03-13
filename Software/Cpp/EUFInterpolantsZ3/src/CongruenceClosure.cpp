#include "CongruenceClosure.h"

CongruenceClosure::CongruenceClosure(const unsigned & min_id, const z3::expr_vector & subterms,
				     PredList & pred_list, UnionFindExplain & uf) :
  min_id(min_id), subterms(subterms), pred_list(pred_list),
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
