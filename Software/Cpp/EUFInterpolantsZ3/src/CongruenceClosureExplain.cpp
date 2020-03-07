#include "CongruenceClosureExplain.h"

CongruenceClosureExplain::CongruenceClosureExplain(const unsigned & min_id, const z3::expr_vector & subterms,
						   CCList & pred_list, UnionFind & uf, CurryDeclarations & curry_decl) :
  CongruenceClosure(min_id, subterms, pred_list, uf), num_terms(subterms.size()), curry_decl(curry_decl){
  
  // --------------------------------------------------
  // The following defines curry_nodes
  curry_nodes.resize(num_terms);
  std::vector<bool> visited(num_terms, false);

  for(unsigned i = min_id; i < num_terms; i++)
    curry_nodes[i] = new CurryNode(i);

  curryfication(subterms[num_terms - 1], visited);
  // --------------------------------------------------

  for(unsigned i = min_id; i < num_terms; i++)
    std::cout << *curry_nodes[i] << std::endl;

  for(auto x : extra_nodes)
    std::cout << *x << std::endl;

  std::cout << "Pending list" << std::endl;
  for(auto x : pending_explain)
    std::cout << x << std::endl;
  
}

CongruenceClosureExplain::~CongruenceClosureExplain(){
  for(unsigned i = min_id; i < num_terms; i++)
    delete curry_nodes[i];
  for(auto x : extra_nodes)
    delete x;
#if DEBUG_DESTRUCTORS_CC
  std::cout << "Done ~CongruenceClosureExplain" << std::endl;
#endif
}

void CongruenceClosureExplain::merge(CurryNode * s, CurryNode * t){
  if(s->isConstant() && t->isConstant()){
    pending_explain.push_back(EquationCurryNodes(s, t));
    // Propagate(); // MISSING:
  }
  else{
    if(true){ // Keep working here
      // Propagate(); // MISSING:
    }
    else{
    }
  }
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
      unsigned last_node_pos = extra_nodes.size(),
    	new_last_node_pos = last_node_pos + num;
      extra_nodes.resize(new_last_node_pos);
      
      for(unsigned i = last_node_pos; i < new_last_node_pos; i++)
	extra_nodes[i] = new CurryNode(i + num_terms, "apply", nullptr, nullptr);
      
      // Case for first argument
      extra_nodes[last_node_pos]->update("apply",
					 curry_decl[f.id()],
					 curry_nodes[e.arg(0).id()]);
      // Case for the rest of the arguments
      for(unsigned i = 1; i < num; i++)
      	extra_nodes[last_node_pos + i]->update("apply",
					       extra_nodes[last_node_pos + i - 1],
					       curry_nodes[e.arg(i).id()]);

      // extra_nodes[new_last_node_pos - 1]->changeId(curry_nodes[e.id()]->getId());
#if DEBUG_CURRYFICATION
      std::cout << "Before (func term) " << *(curry_nodes[e.id()]) << " "
		<< (curry_nodes[e.id()] == extra_nodes[new_last_node_pos - 1]) << std::endl;
#endif
      merge(extra_nodes[new_last_node_pos - 1], curry_nodes[e.id()]);
#if DEBUG_CURRYFICATION
      std::cout << "After (func term) " << *(curry_nodes[e.id()]) << std::endl;
#endif
    }
    else{
#if DEBUG_CURRYFICATION
      std::cout << "Before (constant) " << *(curry_nodes[e.id()]) << " "
		<< (curry_nodes[e.id()] == curry_decl[f.id()]) << std::endl;
#endif
      curry_nodes[e.id()]->update(f.name().str(), nullptr, nullptr);
#if DEBUG_CURRYFICATION
      std::cout << "After (constant) " << *(curry_nodes[e.id()]) << std::endl;
#endif
    }

    switch(f.decl_kind()){
    case Z3_OP_EQ:
      merge(curry_nodes[e.arg(0).id()], curry_nodes[e.arg(1).id()]);
      return;
    default:
      return;
    }
  }
  
  throw "Problem @ EUFInterpolant::curryfication(z3::expr const &). The z3::expr const & is not an app.";
}

void CongruenceClosureExplain::buildCongruenceClosure(std::list<unsigned> & pending){
  throw "CongruenceClosureExplain::buildCongruenceClosure(std::list<unsigned> &). Implementation not defined";
}

std::ostream & operator << (std::ostream & os, const CongruenceClosureExplain & cc){
  return os;
}
