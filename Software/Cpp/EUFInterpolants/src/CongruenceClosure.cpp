#include "CongruenceClosure.h"

#define TRACE_MERGE     false
#define TRACE_COMBINE   false
#define TRACE_PENDING   false
#define TRACE_EC        false
#define TRACE_SIG_TABLE false
#define BEFORE_CC       false
#define AFTER_CC        false

#define DEBUG_CC(X, Y) if(X) { Y }

void CongruenceClosure::init(){
  unsigned lhs, rhs;
  Term * lhs_repr, * rhs_repr;
  for(auto equation : equations){
    lhs = equation.first.id();
    rhs = equation.second.id();
    lhs_repr = getReprTerm(lhs);
    rhs_repr = getReprTerm(rhs);
    
    if(lhs_repr->getLength() < rhs_repr->getLength()){
      merge(rhs_repr, lhs_repr);
      DEBUG_CC(TRACE_MERGE,
	       std::cout << "==========================================" << std::endl;
	       std::cout << "Merging " << std::endl;
	       std::cout << lhs_repr->to_string() << std::endl;
	       std::cout << " to " << std::endl;
	       std::cout << rhs_repr->to_string() << std::endl;
	       std::cout << "==========================================" << std::endl;)
	}
    else{
      merge(lhs_repr, rhs_repr);
      DEBUG_CC(TRACE_MERGE,
	       std::cout << "==========================================" << std::endl;
	       std::cout << "Merging " << std::endl;
	       std::cout << rhs_repr->to_string() << std::endl;
	       std::cout << " to " << std::endl;
	       std::cout << lhs_repr->to_string() << std::endl;
	       std::cout << "==========================================" << std::endl;)
	}
    DEBUG_CC(TRACE_EC,
	     std::cout << "==========================================" << std::endl;
	     std::cout << "Terms and ID's" << std::endl;
	     for(unsigned i = 0; i < Term::getTotalNumTerm(); ++i)
	       std::cout << i << " " << getReprTerm(i)->to_string() << std::endl;
	     std::cout << "==========================================" << std::endl;
	     std::cout << "==========================================" << std::endl;
	     std::cout << "Current Equivalence Class" << std::endl;
	     std::cout << equivalence_class << std::endl;
	     std::cout << "==========================================" << std::endl;)
      }
}

CongruenceClosure::CongruenceClosure(z3::context & ctx, const z3::expr & v) :
  Terms(ctx, v)
{
  init();
}

CongruenceClosure::CongruenceClosure(z3::context & ctx,
				     const z3::expr & v,
				     const std::set<std::string> & symbols_to_elim) :
  Terms(ctx, v, symbols_to_elim)
{
  init();
}

CongruenceClosure::~CongruenceClosure(){}

void CongruenceClosure::buildCongruenceClosure(){
  Pending pending;
  Combine combine;

  // Adding functional grounded vertices to pending
  for(auto term : terms){
    if(term->getArity() >= 1)
      pending.push_back(term);
  }

  DEBUG_CC(BEFORE_CC,
	   std::cout<< "Before Congruence Closure" << std::endl;
	   for(auto x : terms)
	     if(x->to_string()[0] != '_')
	       std::cout << "Term: " << x->to_string()
			 << " Original term id: " << x->getId()
			 << " Representative term id: " << getReprTerm(x)->getId() << std::endl;
	   )
  
  while(!pending.empty()){
    combine.clear();
    for(auto term : pending){
      try{
	Term * already_there = sigTable.query(term, equivalence_class);
	combine.push_back(std::make_pair(term, already_there));
	DEBUG_CC(TRACE_COMBINE,
		 std::cout << "==========================================" << std::endl;
		 std::cout << "Inserting to Combine" << std::endl;
		 std::cout << term->to_string() << " and " << std::endl;
		 std::cout << already_there->to_string() << std::endl;
		 std::cout << "==========================================" << std::endl;)
	  }
      catch (const char * msg){
	sigTable.enter(term, equivalence_class);
	DEBUG_CC(TRACE_SIG_TABLE,
		 std::cout << "==========================================" << std::endl;
		 std::cout << "Current Signature Table" << std::endl;
		 std::cout << sigTable << std::endl;
		 std::cout << "==========================================" << std::endl;)
	  }
    }
    pending.clear();
    for(auto pair_terms : combine){
      Term * v = pair_terms.first,* w = pair_terms.second;
      Term * find_v = getReprTerm(v),* find_w = getReprTerm(w);
      if(find_v != find_w){
	// Invariant find_v->getLength() <= find_w->getLengt()
	if(find_v->getLength() > find_w->getLength()){
	  Term * temp_swap = find_v;
	  find_v = find_w;
	  find_w = temp_swap;
	}
	CircularList<Term*> & list_find_v = find_v->getPredecessors();
	if(find_v->getLength() != 0){
	  auto predecessor_it = list_find_v.begin();
	  do{
	    Term * predecessor = predecessor_it->data;
	    sigTable.remove(predecessor, equivalence_class);
	    pending.push_back(predecessor);
	    predecessor_it = predecessor_it->next;
	  } while(predecessor_it != list_find_v.begin());
	}
	merge(find_w, find_v);
	DEBUG_CC(TRACE_MERGE,
		 std::cout << "========================================" << std::endl;
		 std::cout << "Merging " << std::endl;
		 std::cout << find_w->to_string() << std::endl;
		 std::cout << " to " << std::endl;
		 std::cout << find_v->to_string() << std::endl;
		 std::cout << "========================================" << std::endl;)
	  }
    }
  }
  DEBUG_CC(AFTER_CC,
	   std::cout<< "After Congruence Closure" << std::endl;
	   for(auto x : terms)
	     if(x->to_string()[0] != '_')
	       std::cout << "Term: " << x->to_string()
			 << " Original term id: " << x->getId()
			 << " Representative term id: " << getReprTerm(x)->getId() << std::endl;
	   )
}

bool CongruenceClosure::checkCorrectness(){
  unsigned total_num_vertex = Term::getTotalNumTerm();

  for(unsigned i = 0; i < total_num_vertex - 1; ++i)
    for(unsigned j = i + 1; j < total_num_vertex; ++j){
      Term * u = getReprTerm(i), * v = getReprTerm(j);
      if(u->getArity() == v->getArity()){
	if(u->getArity() == 1
	   && sigTable.getUnarySignature(u, equivalence_class)
	   == sigTable.getUnarySignature(v, equivalence_class)
	   && getReprTerm(u)->getId() != getReprTerm(v)->getId()){
	  std::cout << "Not Ok" << std::endl;
	  return false;
	}
	if(u->getArity() == 2
	   && sigTable.getBinarySignature(u, equivalence_class)
	   == sigTable.getBinarySignature(v, equivalence_class)
	   && getReprTerm(u)->getId() != getReprTerm(v)->getId()){
	  std::cout << "Not Ok" << std::endl;
	  return false;
	}
      }
    }
  std::cout << "Ok" << std::endl;
  return true;
}

std::ostream & operator << (std::ostream & os, CongruenceClosure & cc){
  os << "Congruence Closure" << std::endl;
  unsigned total_num_vertex = Term::getTotalNumTerm();
  
  for(unsigned i = 0; i < total_num_vertex; ++i){
    // Just print non-extra nodes
    auto term = cc.getOriginalTerm(i);
    if(term->getName()[0] != '_')
      os << "Term: " << term->to_string()
	 << " Representative: " << cc.getReprTerm(term)->to_string() << std::endl;
  }
  return os;
}
