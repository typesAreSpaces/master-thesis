#include "Vertex.h"

unsigned Vertex::totalNumVertex = 0;

void Vertex::addPredecessor(unsigned i){
	if(!defined)
		predecessors.add(i);
}

Vertex::Vertex(std::string name, unsigned arity) : name(name), symbolCommonQ(true), defined(false),
																									 id(totalNumVertex), arity(arity){
  ++totalNumVertex;
}

Vertex::Vertex() : symbolCommonQ(true), defined(false),
									 id(totalNumVertex){
  ++totalNumVertex;
									 }

Vertex::~Vertex(){};

void Vertex::setName(std::string _name){
  name = _name;
}

void Vertex::setArity(unsigned _arity){
  arity = _arity;
}

void Vertex::addSuccessor(Vertex * v){
	if(!defined){
		successors.push_back(v);
		v->addPredecessor(id);
	}
}

void Vertex::setSymbolCommonQ(bool b){
  symbolCommonQ = b;
}

void Vertex::mergePredecessors(Vertex * v){
  this->predecessors.merge(v->getPredecessors());
}

void Vertex::define(){
	defined = true;
}

std::string Vertex::getName(){
  return name;
}

std::string Vertex::to_string(){
  if(arity == 0)
    return name;
  std::string _temp = name + "(";
  unsigned _counter = 0;
  for(std::vector<Vertex*>::iterator it = successors.begin();
			it != successors.end(); ++it){
    _temp += (*it)->to_string();
    ++_counter;
    if(_counter < arity)
      _temp += ",";
  }
  return _temp + ")";
}

unsigned Vertex::getArity(){
  return arity;
}

unsigned Vertex::getId(){
  return id;
}

unsigned Vertex::getLength(){
  return predecessors.size();
}

unsigned Vertex::getTotalNumVertex(){
  return totalNumVertex;
}

bool Vertex::getSymbolCommonQ(){
  return symbolCommonQ;
}

std::vector<Vertex*> & Vertex::getSuccessors(){
  return successors;
}

CircularList<unsigned> * Vertex::getPredecessors(){
  return &predecessors;
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
  for(std::vector<Vertex*>::iterator it = successors.begin(); it != successors.end(); ++it){
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
  for(std::vector<Vertex*>::iterator it = v.successors.begin(); it != v.successors.end(); ++it){
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
  if (u.symbolCommonQ < v.symbolCommonQ)
    return true;
  else{
    if(u.symbolCommonQ > v.symbolCommonQ)
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
