#include "CongruenceClosureExplain.h"
#define DEBUG_SANITY_CHECK false

CongruenceClosureExplain::CongruenceClosureExplain(const unsigned & min_id, const z3::expr_vector & subterms,
						   CCList & pred_list, UnionFindExplain & uf,
						   CurryDeclarations & curry_decl, FactoryCurryNodes & factory_curry_nodes) :
  CongruenceClosure(min_id, subterms, pred_list, uf), num_terms(subterms.size()),
  curry_nodes(), extra_nodes(), curry_decl(curry_decl), factory_curry_nodes(factory_curry_nodes),
  pending_explain(), lookup_table(uf), use_list(), class_list_explain(){
  
  // --------------------------------------------------
  // The following defines curry_nodes
  curry_nodes.resize(num_terms);   
  std::vector<bool> visited(num_terms, false);
  
  curryfication(subterms[num_terms - 1], visited);
  // --------------------------------------------------

  factory_curry_nodes.flattening(extra_nodes, num_terms);
  std::cout << factory_curry_nodes << std::endl;

  std::cout << uf << std::endl;
  // KEEP: WORKING here. Update uf with the size of factory_curry_nodes
  // and update it using the merge that are pending!
  
  // std::cout << "Pending list" << std::endl;
  // for(auto x : pending_explain)
  //   std::cout << x << std::endl;
  
}

CongruenceClosureExplain::~CongruenceClosureExplain(){
#if DEBUG_DESTRUCTORS_CC
  std::cout << "Done ~CongruenceClosureExplain" << std::endl;
#endif
}

unsigned CongruenceClosureExplain::addExtraNodes(unsigned num){
  unsigned last_node_pos = extra_nodes.size(),
    new_last_node_pos = last_node_pos + num;
  extra_nodes.resize(new_last_node_pos);
  return new_last_node_pos;
}

void CongruenceClosureExplain::curryfication(z3::expr const & e, std::vector<bool> & visited){
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
      unsigned last_node_pos = extra_nodes.size();
      unsigned new_last_node_pos = addExtraNodes(num);
      
      // Case for first argument
      extra_nodes[last_node_pos] =
	factory_curry_nodes.newCurryNode(last_node_pos + num_terms,
					 "apply",
					 curry_decl[f.id()],
					 curry_nodes[e.arg(0).id()]);
      // Case for the rest of the arguments
      for(unsigned i = 1; i < num; i++)
	extra_nodes[last_node_pos + i] =
	  factory_curry_nodes.newCurryNode(last_node_pos + i + num_terms,
					   "apply",
					   extra_nodes[last_node_pos + i - 1],
					   curry_nodes[e.arg(i).id()]);
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
  
  throw "Problem @ CongruenceClosureExplain::curryfication(z3::expr const &). The z3::expr const & is not an app.";
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
