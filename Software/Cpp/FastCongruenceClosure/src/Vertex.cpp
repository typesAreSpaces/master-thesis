#include "Vertex.h"

unsigned Vertex::totalNumVertex = 0;

unsigned Vertex::getTotalNumVertex(){
  return totalNumVertex;
}

void Vertex::addPredecessor(unsigned i){
  predecessors.add(i);
}
Vertex::Vertex(std::string name, unsigned arity) : name(name), arity(arity), id(totalNumVertex){
  ++totalNumVertex;
}
Vertex::Vertex() : id(totalNumVertex){
  ++totalNumVertex;
};
Vertex::~Vertex(){};
void Vertex::setName(std::string _name){
  name = _name;
}
void Vertex::setArity(unsigned _arity){
  arity = _arity;
}
void Vertex::addSuccessor(Vertex * v){
  successors.push_back(v);
  v->addPredecessor(id);
}
std::vector<Vertex*> & Vertex::getSuccessors(){
  return successors;
}

CircularList<unsigned> * Vertex::getPredecessors(){
  return &predecessors;
}

unsigned Vertex::getId(){
  return id;
}

unsigned Vertex::getArity(){
  return arity;
}

std::string Vertex::getName(){
  return name;
}

unsigned Vertex::getLength(){
  return predecessors.size();
}

void Vertex::mergePredecessors(Vertex * v){
  this->predecessors.mergeCircularList(v->getPredecessors());
}

std::string Vertex::to_string(){
  if(arity == 0)
    return name;
  std::string _temp = name + "(";
  unsigned _counter = 0;
  for(std::vector<Vertex*>::iterator it = successors.begin(); it != successors.end(); ++it){
    _temp += (*it)->to_string();
    ++_counter;
    if(_counter < arity)
      _temp += ",";
  }
  return _temp + ")";
}

std::ostream & Vertex::ss (std::ostream & os){
  if(arity == 0){
    os << name;
    return os;
  }
  os << name << "(";
  unsigned _counter = 0;
  for(std::vector<Vertex*>::iterator it = successors.begin(); it != successors.end(); ++it){
    (*it)->ss(os);
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
  v.predecessors.print(os);
  os << "Successors:" << std::endl;
  for(std::vector<Vertex*>::iterator it = v.successors.begin(); it != v.successors.end(); ++it){
    os << (*it)->to_string();
    ++_counter;
    if(_counter < v.arity)
      os << ", ";
  }
  return os;
}
