#include "CongruenceClosureExplain.h"
#define DEBUG_SANITY_CHECK false

CongruenceClosureExplain::CongruenceClosureExplain(const unsigned & min_id, const z3::expr_vector & subterms,
						   CCList & pred_list, UnionFind & uf, CurryDeclarations & curry_decl) :
  CongruenceClosure(min_id, subterms, pred_list, uf), num_terms(subterms.size()), curry_decl(curry_decl),
  lookup_table(uf){
  
  // --------------------------------------------------
  // The following defines curry_nodes
  curry_nodes.resize(num_terms);   
  std::vector<bool> visited(num_terms, false);
  
  curryfication(subterms[num_terms - 1], visited);
  // --------------------------------------------------

#if DEBUG_SANITY_CHECK
  std::cout << "--Curry nodes" << std::endl;
  for(unsigned i = min_id; i < num_terms; i++){
    std::cout << *curry_nodes[i] << std::endl;
  }
  
  std::cout << "--Extra nodes" << std::endl;
  for(auto x : extra_nodes)
    std::cout << *x << std::endl;
#endif

  for(auto x : to_replace){
    std::cout << *CurryNode::hash_table[x] << std::endl;
  }
  
  // std::cout << "Pending list" << std::endl;
  // for(auto x : pending_explain)
  //   std::cout << x << std::endl;
  
}

CongruenceClosureExplain::~CongruenceClosureExplain(){
#if DEBUG_DESTRUCTORS_CC
  std::cout << "Done ~CongruenceClosureExplain" << std::endl;
#endif
}

void CongruenceClosureExplain::curryfication(z3::expr const & e,
					     std::vector<bool> & visited){
#if DEBUG_CURRYFICATION
  std::cout << "curryfing this " << e << " " << e.id() << std::endl;
#endif
  if(e.is_app()){

    if(visited[e.id()])
      return;
    visited[e.id()] = true;
    
    unsigned num = e.num_args();
    auto f = e.decl();
    
    for(unsigned i = 0; i < num; i++)
      curryfication(e.arg(i), visited);
    
    // Update curry_nodes
    if(num > 0){
      unsigned last_node_pos = extra_nodes.size(), new_last_node_pos = last_node_pos + num;
      extra_nodes.resize(new_last_node_pos);
      uf.increaseSize(new_last_node_pos + num_terms);
      
      // Case for first argument
      extra_nodes[last_node_pos] = CurryNode::newCurryNode(last_node_pos + num_terms,
							   "apply",
							   curry_decl[f.id()],
							   curry_nodes[e.arg(0).id()]);
      if(extra_nodes[last_node_pos]->isReplaceable())
	to_replace.insert(extra_nodes[last_node_pos]->hash());
      
      // Case for the rest of the arguments
      for(unsigned i = 1; i < num; i++){
	extra_nodes[last_node_pos + i] = CurryNode::newCurryNode(last_node_pos + i + num_terms,
								 "apply",
								 extra_nodes[last_node_pos + i - 1],
								 curry_nodes[e.arg(i).id()]);
	// KEEP: Working here
	predecessors[extra_nodes[last_node_pos + i - 1]].push_back(extra_nodes[last_node_pos + i]);
      }
      
      curry_nodes[e.id()] = extra_nodes[new_last_node_pos - 1];
    }
    else
      curry_nodes[e.id()] = curry_decl[f.id()];

    switch(f.decl_kind()){
    case Z3_OP_EQ:
      // This approach is obsolete
      // CHANGE: THIS using reprs 
      // merge(curry_nodes[e.arg(0).id()]->getId(), curry_nodes[e.arg(1).id()]->getId());
      return;
    default:
      return;
    }
  }
  
  throw "Problem @ EUFInterpolant::curryfication(z3::expr const &). The z3::expr const & is not an app.";
}

void CongruenceClosureExplain::merge(CurryNode * s, CurryNode * t){
  if(s->isConstant() && t->isConstant()){
    pending_explain.push_back(EquationCurryNodes(s, t, CONST_EQ));
    propagate();
  }
  else{
    try {
      std::cout << "--------------" << std::endl;
      std::cout << *s << std::endl;
      std::cout << *t << std::endl;
      std::cout << "--------------" << std::endl;

      EquationCurryNodes whatever = lookup_table.query(0, 1);  // WRONG: Incomplete implementation
      
      std::cout << whatever << std::endl;
      pending_explain.push_back(EquationCurryNodes(s, t, APPLY_EQ));
      propagate();
    }
    catch(...){
      lookup_table.enter(0, 1, EquationCurryNodes(nullptr, nullptr, APPLY_EQ)); // WRONG: Incomplete implementation
      // Update UseLists!!!
    }
  }
}

void CongruenceClosureExplain::propagate(){
  while(!pending_explain.empty()){
    auto eq = pending_explain.front();
    pending_explain.pop_front();

    switch(eq.kind_equation){
    case CONST_EQ:
      break;
    case APPLY_EQ:
      break;
    }

    
    
  }
}

void CongruenceClosureExplain::buildCongruenceClosure(std::list<unsigned> & pending){
  throw "CongruenceClosureExplain::buildCongruenceClosure(std::list<unsigned> &). Implementation not defined";
}

std::ostream & operator << (std::ostream & os, const CongruenceClosureExplain & cc){
  return os;
}
