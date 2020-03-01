#include "CongruenceClosureNO.h"

CongruenceClosureNO::CongruenceClosureNO(const unsigned & min_id, const z3::expr_vector & subterms,
					   CCList & cc_list, UnionFind & uf) :
  CongruenceClosure(min_id, subterms, cc_list, uf){
}

CongruenceClosureNO::~CongruenceClosureNO(){
#if DEBUG_DESTRUCTORS_CC
  std::cout << "Done ~CongruenceClosureNO" << std::endl;
#endif
}

void CongruenceClosureNO::buildCongruenceClosure(std::list<unsigned> & pending){
  // Implement Nelson-Oppen Congruence Closure
}

std::ostream & operator << (std::ostream & os, const CongruenceClosureNO & cc){
  return os;
}
