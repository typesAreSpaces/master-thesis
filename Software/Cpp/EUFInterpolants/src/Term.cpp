#include "Term.h"

unsigned Term::total_num_vertex = 0;

Term::Term(std::string name,
	   unsigned arity) : name(name),
			     is_symbol_common(true),
			     is_defined(false),
			     id(total_num_vertex),
			     arity(arity){
  ++total_num_vertex;
			     }

Term::Term() : is_symbol_common(true),
	       is_defined(false),
	       id(total_num_vertex){
  ++total_num_vertex;
	       }

Term::~Term(){};

void Term::setName(std::string name){
  this->name = name;
}

void Term::setSymbolCommonQ(bool is_symbol_common){
  this->is_symbol_common = is_symbol_common;
}

void Term::define(){
  is_defined = true;
}

void Term::setArity(unsigned arity){
  this->arity = arity;
}

void Term::addSuccessor(Term * v){
  assert(!is_defined);
  successors.push_back(v);
  // Add predeccessors
  v->predecessors.add(this);
}

void Term::mergePredecessors(Term * v){
  this->predecessors.merge(v->getPredecessors());
}

unsigned Term::getTotalNumTerm(){
  return total_num_vertex;
}

const std::string & Term::getName(){
  return name;
}

bool Term::getSymbolCommonQ(){
  return is_symbol_common;
}

unsigned Term::getId(){
  return id;
}

unsigned Term::getArity(){
  return arity;
}

unsigned Term::getLength(){
  return predecessors.size();
}

const std::vector<Term*> & Term::getSuccessors(){
  return successors;
}

CircularList<Term*> & Term::getPredecessors(){
  return predecessors;
}

std::string Term::to_string(){
  if(arity == 0)
    return name;
  std::string partial_name = name + "(";
  unsigned _counter = 0;
  for(auto it = successors.begin();
      it != successors.end(); ++it){
    partial_name += (*it)->to_string();
    ++_counter;
    if(_counter < arity)
      partial_name += ",";
  }
  return partial_name + ")";
}

Term * Term::getLeftChild(){
  assert(successors[0] != nullptr);
  return successors[0];
}

Term * Term::getRightChild(){
  assert(successors[1] != nullptr);
  return successors[1];
}

std::ostream & Term::functionPrettyPrint (std::ostream & os){
  if(arity == 0){
    os << name;
    return os;
  }
  os << name << "(";
  unsigned _counter = 0;
  for(auto it = successors.begin(); it != successors.end(); ++it){
    (*it)->functionPrettyPrint(os);
    ++_counter;
    if(_counter < arity)
      os << ",";
  }
  os << ")";
  return os;
}

std::ostream & operator << (std::ostream & os, Term & v){
  unsigned _counter = 0;
  os << "Symbol: " << v.to_string();
  os << " ID: " << v.id;
  os << " Predecessors: ";
  os << v.predecessors << std::endl;
  os << " Successors: ";
  for(auto it = v.successors.begin();
      it != v.successors.end(); ++it){
    os << (*it)->id;
    ++_counter;
    if(_counter < v.arity)
      os << ", ";
  }
  return os;
}

bool operator ==(const Term & u, const Term & v){
  return (u.id == v.id);
}

bool operator !=(const Term & u, const Term & v){
  return !(u == v);
}

bool operator < (const Term & u, const Term & v){
  if (u.is_symbol_common < v.is_symbol_common)
    return true;
  else{
    if(u.is_symbol_common > v.is_symbol_common)
      return false;
    else{
      if(u.arity <  v.arity)
	return true;
      else{
	if(u.arity > v.arity)
	  return false;
	else
	  return (u.id < v.id);
      }
    }
  }
}

bool operator <= (const Term & u, const Term & v){
  return (u == v || u < v);
}

bool operator >(const Term & u, const Term & v){
  return (v < u);
}
bool operator >=(const Term & u, const Term & v){
  return (u == v || u > v);
}
