#include "Vertex.h"

unsigned Vertex::total_num_vertex = 0;

Vertex::Vertex(std::string name, unsigned arity) : name(name),
						   is_symbol_common(true),
						   defined(false),
						   id(total_num_vertex),
						   arity(arity){
  ++total_num_vertex;
						   }

Vertex::Vertex() : is_symbol_common(true),
		   defined(false),
		   id(total_num_vertex){
  ++total_num_vertex;
		   }

Vertex::~Vertex(){};

void Vertex::setName(std::string name){
  this->name = name;
}

void Vertex::setSymbolCommonQ(bool is_symbol_common){
  this->is_symbol_common = is_symbol_common;
}

void Vertex::define(){
  defined = true;
}

void Vertex::setArity(unsigned arity){
  this->arity = arity;
}

void Vertex::addPredecessor(unsigned i){
  if(!defined)
    predecessors.add(i);
}

void Vertex::addSuccessor(Vertex * v){
  if(!defined){
    successors.push_back(v);
    v->addPredecessor(id);
  }
}

void Vertex::mergePredecessors(Vertex * v){
  this->predecessors.merge(v->getPredecessors());
}

unsigned Vertex::getTotalNumVertex(){
  return total_num_vertex;
}

std::string Vertex::getName(){
  return name;
}

bool Vertex::getSymbolCommonQ(){
  return is_symbol_common;
}

unsigned Vertex::getId(){
  return id;
}

unsigned Vertex::getArity(){
  return arity;
}

unsigned Vertex::getLength(){
  return predecessors.size();
}

std::vector<Vertex*> & Vertex::getSuccessors(){
  return successors;
}

CircularList<unsigned> * Vertex::getPredecessors(){
  return &predecessors;
}

std::string Vertex::to_string(){
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

Vertex * Vertex::getLeftChild(){
  return successors[0];
}

Vertex * Vertex::getRightChild(){
  return successors[1];
}

std::ostream & Vertex::functionPrettyPrint (std::ostream & os){
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

std::ostream & operator << (std::ostream & os, Vertex & v){
  unsigned _counter = 0;
  os << "Symbol: " << v.to_string() << std::endl;
  os << "ID: " << v.id << std::endl;
  os << "Predecessors:" << std::endl;
  os << v.predecessors << std::endl;
  os << "Successors:" << std::endl;
  for(auto it = v.successors.begin();
      it != v.successors.end(); ++it){
    os << (*it)->to_string();
    ++_counter;
    if(_counter < v.arity)
      os << ", ";
  }
  return os;
}

bool operator ==(const Vertex & u, const Vertex & v){
  return (u.id == v.id);
}

bool operator !=(const Vertex & u, const Vertex & v){
  return !(u == v);
}

bool operator < (const Vertex & u, const Vertex & v){
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

bool operator <= (const Vertex & u, const Vertex & v){
  return (u == v || u < v);
}

bool operator >(const Vertex & u, const Vertex & v){
  return (v < u);
}
bool operator >=(const Vertex & u, const Vertex & v){
  return (u == v || u > v);
}
