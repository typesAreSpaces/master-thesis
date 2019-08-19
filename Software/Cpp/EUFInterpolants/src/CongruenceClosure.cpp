#include "CongruenceClosure.h"

#define traceMerge    false
#define traceCombine  false
#define tracePending  false
#define traceEC       false
#define traceSigTable false

#define DEBUG_CC(X, Y) if(X) { Y }

void CongruenceClosure::init(Z3_context c){
  unsigned lhs, rhs;
  Term * lhs_vertex, * rhs_vertex;
  for(auto equation = equations.begin(); equation != equations.end(); ++equation){
    lhs = Z3_get_ast_id(c, equation->first);
    rhs = Z3_get_ast_id(c, equation->second);
    lhs_vertex = getTerm(lhs);
    rhs_vertex = getTerm(rhs);
    
    if(lhs_vertex->getLength() < rhs_vertex->getLength()){
      merge(getTerm(rhs), getTerm(lhs));
      DEBUG_CC(traceMerge,
	       std::cout << "==========================================" << std::endl;
	       std::cout << "Merging " << std::endl;
	       std::cout << lhs_vertex->to_string() << std::endl;
	       std::cout << " to " << std::endl;
	       std::cout << rhs_vertex->to_string() << std::endl;
	       std::cout << "==========================================" << std::endl;)
	}
    else{
      merge(getTerm(lhs), getTerm(rhs));
      DEBUG_CC(traceMerge,
	       std::cout << "==========================================" << std::endl;
	       std::cout << "Merging " << std::endl;
	       std::cout << rhs_vertex->to_string() << std::endl;
	       std::cout << " to " << std::endl;
	       std::cout << lhs_vertex->to_string() << std::endl;
	       std::cout << "==========================================" << std::endl;)
	}
    DEBUG_CC(traceEC,
	     std::cout << "==========================================" << std::endl;
	     std::cout << "Terms and ID's" << std::endl;
	     for(unsigned i = 0; i < Term::getTotalNumTerm(); ++i)
	       std::cout << i << " " << getTerm(i)->to_string() << std::endl;
	     std::cout << "==========================================" << std::endl;
	     std::cout << "==========================================" << std::endl;
	     std::cout << "Current Equivalence Class" << std::endl;
	     std::cout << equivalence_class << std::endl;
	     std::cout << "==========================================" << std::endl;)
      }
}

CongruenceClosure::CongruenceClosure(Z3_context c,
				     Z3_ast v,
				     std::set<std::string> & symbols_to_elim) :
  SignatureTable(c, v, symbols_to_elim) {
  init(c);
}

CongruenceClosure::CongruenceClosure(Z3_context c, Z3_ast v) :
  SignatureTable(c, v) {
  init(c);
}

CongruenceClosure::CongruenceClosure(std::istream & in) : SignatureTable(in) {
  unsigned num_eq, lhs, rhs;
  Term * lhs_vertex, *rhs_vertex;
	
  in >> num_eq;
  for(unsigned i = 0; i < num_eq; ++i){
    in >> lhs >> rhs;
    lhs_vertex = getTerm(lhs);
    rhs_vertex = getTerm(rhs);
    
    if(lhs_vertex->getLength() < rhs_vertex->getLength()){
      merge(getTerm(rhs), getTerm(lhs));
      DEBUG_CC(traceMerge,
	       std::cout << "==========================================" << std::endl;
	       std::cout << "Merging " << std::endl;
	       std::cout << lhs_vertex->to_string() << std::endl;
	       std::cout << " to " << std::endl;
	       std::cout << rhs_vertex->to_string() << std::endl;
	       std::cout << "==========================================" << std::endl;)
	}
    else{
      merge(getTerm(lhs), getTerm(rhs));
      DEBUG_CC(traceMerge,
	       std::cout << "==========================================" << std::endl;
	       std::cout << "Merging " << std::endl;
	       std::cout << rhs_vertex->to_string() << std::endl;
	       std::cout << " to " << std::endl;
	       std::cout << lhs_vertex->to_string() << std::endl;
	       std::cout << "==========================================" << std::endl;)
	}
    DEBUG_CC(traceEC,
	     std::cout << "==========================================" << std::endl;
	     std::cout << "Terms and ID's" << std::endl;
	     for(unsigned i = 0; i < Term::getTotalNumTerm(); ++i)
	       std::cout << i << " " << getTerm(i)->to_string() << std::endl;
	     std::cout << "==========================================" << std::endl;
	     std::cout << "==========================================" << std::endl;
	     std::cout << "Current Equivalence Class" << std::endl;
	     std::cout << equivalence_class << std::endl;
	     std::cout << "==========================================" << std::endl;)
      }
}

CongruenceClosure::~CongruenceClosure(){}

void CongruenceClosure::algorithm(){
  Pending pending;
  Combine combine;
  unsigned total_num_vertex = Term::getTotalNumTerm();

  // Adding functional grounded vertices to pending
  for(unsigned i = 0; i < total_num_vertex; ++i){
    Term * temp_vertex = getTerm(i);
    if(temp_vertex->getArity() >= 1)
      pending.insert(temp_vertex);
  }
	
  while(!pending.empty()){
    combine.clear();
    for(Pending::iterator vertex_it = pending.begin();
	vertex_it != pending.end(); ++vertex_it){
      try{
	Term * already_there = query(*vertex_it);
	combine.insert(std::make_pair(*vertex_it, already_there));
	DEBUG_CC(traceCombine,
		 std::cout << "==========================================" << std::endl;
		 std::cout << "Inserting to Combine" << std::endl;
		 std::cout << (*vertex_it)->to_string() << " and " << std::endl;
		 std::cout << already_there->to_string() << std::endl;
		 std::cout << "==========================================" << std::endl;)
	  }
      catch (const char * msg){
	enter(*vertex_it);
	DEBUG_CC(traceSigTable,
		 std::cout << "==========================================" << std::endl;
		 std::cout << "Current Signature Table" << std::endl;
		 std::cout << *dynamic_cast<SignatureTable*>(this) << std::endl;
		 std::cout << "==========================================" << std::endl;)
	  }
    }
    pending.clear();
    for(Combine::iterator pair = combine.begin();
	pair != combine.end(); ++pair){
      Term * v = pair->first,
	* w = pair->second,
	* find_v = getTerm(v),
	* find_w = getTerm(w);
      if(find_v != find_w){
	if(find_v->getLength() >= find_w->getLength()){
	  Term * temp_swap = find_v;
	  find_v = find_w;
	  find_w = temp_swap;
	}
	CircularList<Term*> & list_find_v = find_v->getPredecessors();
	if(find_v->getLength() != 0){
	  auto predecessor_it = list_find_v.begin();
	  do{
	    Term * predecessor = getOriginalTerm((*predecessor_it).data);
	    // Term * predecessor = getTerm((*predecessor_it).data);
	    remove(predecessor);
	    pending.insert(predecessor);
	    ++predecessor_it;
	  } while(predecessor_it != list_find_v.begin());
	}
	merge(find_w, find_v);
	DEBUG_CC(traceMerge,
		 std::cout << "========================================" << std::endl;
		 std::cout << "Merging " << std::endl;
		 std::cout << find_w->to_string() << std::endl;
		 std::cout << " to " << std::endl;
		 std::cout << find_v->to_string() << std::endl;
		 std::cout << "========================================" << std::endl;)
	  }
    }
  }
}

bool CongruenceClosure::checkCorrectness(){
  unsigned total_num_vertex = Term::getTotalNumTerm();

  for(unsigned i = 0; i < total_num_vertex - 1; ++i)
    for(unsigned j = i + 1; j < total_num_vertex; ++j){
      Term * u = getTerm(i), * v = getTerm(j);
      if(u->getArity() == v->getArity()){
	if(u->getArity() == 1
	   && getUnarySignature(u) == getUnarySignature(v)
	   && getTerm(u)->getId() != getTerm(v)->getId()){
	  std::cout << "Not Ok" << std::endl;
	  return false;
	}
	if(u->getArity() == 2
	   && getBinarySignature(u) == getBinarySignature(v)
	   && getTerm(u)->getId() != getTerm(v)->getId()){
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
	 << " Representative: " << cc.getTerm(term)->to_string() << std::endl;
  }
  return os;
}
