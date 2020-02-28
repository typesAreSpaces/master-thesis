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

void CongruenceClosure::buildCongruenceClosure(std::list<unsigned> & pending){
  std::list<std::pair<unsigned, unsigned> > combine;
  while(!pending.empty()){
    combine.clear();
    for(auto v_id : pending){
      z3::expr v = subterms[v_id];
      try{
	auto w_id = sig_table.query(v);
	combine.push_back(std::make_pair(v_id, w_id));
      }
      catch(...){
	sig_table.enter(v);
      }
    }
    pending.clear();
    for(auto v_w : combine){
      unsigned v = v_w.first, w = v_w.second;
      if(uf.find(v) != uf.find(w)){
	unsigned aux;
	// Invariant: v is always the repr
	if(cc_list[uf.find(v)].size() < cc_list[uf.find(w)].size()){
	  aux = v;
	  v = w;
	  w = aux;
	}
	if(HornClause::compareTerm(subterms[uf.find(v)], subterms[uf.find(w)])){
	  aux = v;
	  v = w;
	  w = aux;
	}
	for(auto u : cc_list[w]){
	  sig_table.erase(subterms[u]);
	  pending.push_back(u);
	}
	uf.combine(uf.find(v), uf.find(w));
	cc_list[uf.find(v)].splice(cc_list[uf.find(v)].end(), cc_list[uf.find(w)]);
      }
    }
  }
}

std::ostream & operator << (std::ostream & os, const CongruenceClosure & cc){
  return os;
}
