#include "CongruenceClosureDST.h"

CongruenceClosureDST::CongruenceClosureDST(const unsigned & min_id, const z3::expr_vector & subterms,
					   PredList & pred_list, UnionFindExplain & uf) :
  CongruenceClosure(min_id, subterms, pred_list, uf){
}

CongruenceClosureDST::~CongruenceClosureDST(){
#if DEBUG_DESTRUCTORS_CC
  std::cout << "Done ~CongruenceClosureDST" << std::endl;
#endif
}

void CongruenceClosureDST::buildCongruenceClosure(std::list<unsigned> & pending){
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
      unsigned v_repr = uf.find(v_w.first), w_repr = uf.find(v_w.second);
      if(v_repr != w_repr){
	unsigned aux;
	// Invariant: v_repr is always the representative of the union
	if(pred_list[v_repr].size() < pred_list[w_repr].size()){
	  aux = v_repr;
	  v_repr = w_repr;
	  w_repr = aux;
	}
	if(HornClause::compareTerm(subterms[v_repr], subterms[w_repr])){
	  aux = v_repr;
	  v_repr = w_repr;
	  w_repr = aux;
	}
	for(auto u : pred_list[w_repr]){
	  sig_table.erase(subterms[u]);
	  pending.push_back(u);
	}
	uf.combine(v_repr, w_repr);
	pred_list[v_repr].splice(pred_list[v_repr].end(), pred_list[w_repr]);
      }
    }
  }
}

std::ostream & operator << (std::ostream & os, const CongruenceClosureDST & cc){
  return os;
}
