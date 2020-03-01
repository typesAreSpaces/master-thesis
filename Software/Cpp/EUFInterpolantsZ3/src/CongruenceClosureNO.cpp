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
  throw "CongruenceClosureNO::buildCongruenceClosure(std::list<unsigned> &). Implementation not defined";
}

void CongruenceClosureNO::buildCongruenceClosure(){
  
}

void CongruenceClosureNO::combine(unsigned u, unsigned v){
  if(uf.find(u) == uf.find(v))
    return;
  auto p_u = cc_list[u], p_v = cc_list[v];
  uf.combine(u, v);
  for(auto x : p_u)
    for(auto y : p_v)
      if(uf.find(x) != uf.find(y) && isCongruent(x,y))
	combine(x, y);
  return;
}

bool CongruenceClosureNO::isCongruent(unsigned x, unsigned y){
  auto term_x = subterms[x], term_y = subterms[y];
  if(sig_table.hash_z3expr(term_x) != sig_table.hash_z3expr(term_y))
    return false;
  assert(term_x.num_args() == term_y.num_args());
  unsigned num_args = term_x.num_args();
  for(unsigned i = 0; i < num_args; i++)
    if(uf.find(term_x.arg(i)) != uf.find(term_y.arg(i)))
      return false;
  return true;
}

std::ostream & operator << (std::ostream & os, const CongruenceClosureNO & cc){
  return os;
}
