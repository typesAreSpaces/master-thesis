#include "CongruenceClosure.h"

#define TRACE_MERGE       false
#define TRACE_COMBINE     false
#define TRACE_PENDING     false
#define TRACE_EC          false
#define TRACE_SIG_TABLE   false
#define BEFORE_CC         false
#define AFTER_CC          false
#define CHECK_CORRECTNESS false

void CongruenceClosure::init(){
  // Parsing the equation
  // Equation Z3 -> Id's in equivalence class -> Internal representation 
  unsigned lhs, rhs;
  Term * lhs_repr, * rhs_repr;
  for(auto equation : equations){
    lhs = equation.first.id();
    rhs = equation.second.id();
    lhs_repr = getReprTerm(lhs);
    rhs_repr = getReprTerm(rhs);
    
    if(lhs_repr->getLength() < rhs_repr->getLength()){
      merge(rhs_repr, lhs_repr);
#if TRACE_MERGE
      std::cout << "==========================================" << std::endl;
      std::cout << "Merging " << std::endl;
      std::cout << lhs_repr->to_string() << std::endl;
      std::cout << " to " << std::endl;
      std::cout << rhs_repr->to_string() << std::endl;
      std::cout << "==========================================" << std::endl;
#endif
    }
    else{
      merge(lhs_repr, rhs_repr);
#if TRACE_MERGE
      std::cout << "==========================================" << std::endl;
      std::cout << "Merging " << std::endl;
      std::cout << rhs_repr->to_string() << std::endl;
      std::cout << " to " << std::endl;
      std::cout << lhs_repr->to_string() << std::endl;
      std::cout << "==========================================" << std::endl;
#endif
    }
#if TRACE_EC
    std::cout << "==========================================" << std::endl;
    std::cout << "Terms and ID's" << std::endl;
    for(unsigned i = 0; i < Term::getTotalNumTerm(); ++i)
      std::cout << i << " " << getReprTerm(i)->to_string() << std::endl;
    std::cout << "==========================================" << std::endl;
    std::cout << "==========================================" << std::endl;
    std::cout << "Current Equivalence Class" << std::endl;
    std::cout << equivalence_class << std::endl;
    std::cout << "==========================================" << std::endl;
#endif
  }
  buildCongruenceClosure();
}

CongruenceClosure::CongruenceClosure(z3::context & ctx, const z3::expr & v) :
  Terms(ctx, v)
{
  init();
}

CongruenceClosure::CongruenceClosure(z3::context & ctx,
				     const z3::expr & v,
				     const UncommonSymbols & symbols_to_elim) :
  Terms(ctx, v, symbols_to_elim)
{
  init();
}

CongruenceClosure::~CongruenceClosure(){
}

void CongruenceClosure::buildCongruenceClosure(){
  Pending pending;
  Combine combine;

  // Adding functional grounded vertices to pending
  for(auto term : terms){
    if(term->getArity() >= 1)
      pending.push_back(term);
  }

#if BEFORE_CC
  std::cout<< "Before Congruence Closure" << std::endl;
  for(auto x : terms)
    if(x->to_string()[0] != '_')
      std::cout << "Term: " << x->to_string()
		<< " Original term id: " << x->getId()
		<< " Representative term id: " << getReprTerm(x)->getId() << std::endl;
#endif
  
  while(!pending.empty()){
    
    combine.clear();
    for(auto term : pending){
      try{
	Term * already_there = sigTable.query(term, equivalence_class);
	combine.push_back(std::make_pair(term, already_there));
#if TRACE_COMBINE
	std::cout << "==========================================" << std::endl;
	std::cout << "Inserting to Combine" << std::endl;
	std::cout << term->to_string() << " and " << std::endl;
	std::cout << already_there->to_string() << std::endl;
	std::cout << "==========================================" << std::endl;
#endif
      }
      catch (const char * msg){
	sigTable.enter(term, equivalence_class);
#if TRACE_SIG_TABLE
	std::cout << "==========================================" << std::endl;
	std::cout << "Current Signature Table" << std::endl;
	std::cout << sigTable << std::endl;
	std::cout << "==========================================" << std::endl;
#endif
      }
    }
    
    pending.clear();
    for(auto pair_terms : combine){
      Term * v = pair_terms.first,* w = pair_terms.second;
      Term * repr_v = getReprTerm(v),* repr_w = getReprTerm(w);
      if(repr_v != repr_w){
	// Invariant repr_v->getLength() <= repr_w->getLengt()
	if(repr_v->getLength() > repr_w->getLength()){
	  Term * temp_swap = repr_v;
	  repr_v = repr_w;
	  repr_w = temp_swap;
	}
	auto & list_repr_v = repr_v->getPredecessors();
	if(repr_v->getLength() != 0){
	  CircularList<Term*>::iterator predecessor_it(list_repr_v.begin());
	  do{
	    auto predecessor = (*predecessor_it).data;
	    sigTable.remove(predecessor, equivalence_class);
	    pending.push_back(predecessor);
	    ++predecessor_it;
	  } while(predecessor_it != list_repr_v.begin());
	}
	merge(repr_w, repr_v);
#if TRACE_MERGE
	std::cout << "========================================" << std::endl;
	std::cout << "Merging " << std::endl;
	std::cout << repr_w->to_string() << std::endl;
	std::cout << " to " << std::endl;
	std::cout << repr_v->to_string() << std::endl;
	std::cout << "========================================" << std::endl;
#endif
      }
    }
  }
  
#if AFTER_CC
  std::cout<< "After Congruence Closure" << std::endl;
  for(auto x : terms)
    if(x->to_string()[0] != '_')
      std::cout << "Term: " << x->to_string()
		<< " Original term id: " << x->getId()
		<< " Representative term id: " << getReprTerm(x)->getId() << std::endl;
#endif
}

bool CongruenceClosure::checkCorrectness(){
  unsigned total_num_vertex = Term::getTotalNumTerm();

  for(unsigned i = 0; i < total_num_vertex - 1; ++i)
    for(unsigned j = i + 1; j < total_num_vertex; ++j){
      Term * u = getReprTerm(i), * v = getReprTerm(j);
      if(u->getArity() == v->getArity()){
	switch(u->getArity()){
	case 0:
	  // This method just checks if the congruence
	  // closure is correctly computed for nodes/terms
	  // with arity > 0
	  break;
	case 1:
	  if(sigTable.getUnarySignature(u, equivalence_class)
	     == sigTable.getUnarySignature(v, equivalence_class)
	     && getReprTerm(u)->getId() != getReprTerm(v)->getId()){
#if CHECK_CORRECTNESS
	    std::cout << "Not Ok (Case arity 1)" << std::endl;
#endif
	    return false;
	  }
	  break;
	case 2:
	  if(sigTable.getBinarySignature(u, equivalence_class)
	     == sigTable.getBinarySignature(v, equivalence_class)
	     && getReprTerm(u)->getId() != getReprTerm(v)->getId()){
#if CHECK_CORRECTNESS
	    std::cout << "Not Ok (Case arity 2)" << std::endl;
#endif
	    return false;
	  }
	  break;
	default:
#if CHECK_CORRECTNESS
	  std::cout << "Incorrect arities" << std::endl;
#endif
	  return false;
	  break;
	}
      }
    }
#if CHECK_CORRECTNESS
  std::cout << "Ok" << std::endl;
#endif
  return true;
}

void CongruenceClosure::transferEqClassAndPreds(const CongruenceClosure & cc){
  this->transferEqClass(cc);
  this->transferPreds(cc);
}

void CongruenceClosure::transferEqClass(const CongruenceClosure & cc){
  // Transfering equivalence class
  equivalence_class = cc.getDeepEquivalenceClass();
}

void CongruenceClosure::transferPreds(const CongruenceClosure & cc){
  // Transfering predecessors
  unsigned num_terms = terms.size();
  for(unsigned index = 0; index < num_terms; ++index){
    CircularList<Term*> & pred = terms[index]->getPredecessors();
    CircularList<Term*> & cc_pred = cc.getOriginalTerm(index)->getPredecessors();
    pred.~CircularList();
    if(!cc_pred.empty()){
      CircularList<Term*>::iterator pred_iterator(cc_pred.begin());
      do{
	pred.add(terms[((*pred_iterator).data)->getId()]);
	++pred_iterator;
      } while(pred_iterator != cc_pred.begin());
    }
  }
}

const SymbolLocations & CongruenceClosure::getSymbolLocations(){
  return symbol_locations;
}

std::ostream & operator << (std::ostream & os, CongruenceClosure & cc){
  os << "Congruence Closure" << std::endl;
  for(auto term : cc.terms){
    if(term->getName()[0] != '_')
      os << "ID: " << term->getId()
	 << ", Term: " << term->to_string()
	 << ", Common: " << term->getSymbolCommonQ()
	 << ", Representative: " << cc.getReprTerm(term->getId())->to_string()
	 << std::endl;
  }
  return os;
}
