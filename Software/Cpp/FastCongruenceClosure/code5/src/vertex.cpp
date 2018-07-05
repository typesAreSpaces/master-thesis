#include "vertex.h"

int Vertex::totalNumVertex = 0;
Vertex::Vertex(std::string name, int arity) : name(name), arity(arity), id(totalNumVertex){
  ++totalNumVertex;
}
Vertex::Vertex() : id(totalNumVertex){
  ++totalNumVertex;
};
Vertex::~Vertex(){};
void Vertex::setName(std::string _name){
  name = _name;
}
void Vertex::setArity(int _arity){
  arity = _arity;
}
void Vertex::addSuccessor(Vertex * v){
  successors.push_back(v);
}
std::vector<Vertex*> & Vertex::getSuccessors(){
  return successors;
}

int Vertex::getId(){
  return id;
}

std::string Vertex::to_string(){
  if(arity == 0)
    return name;
  std::string _temp = name + "(";
  int _counter = 0;
  for(std::vector<Vertex*>::iterator it = successors.begin(); it != successors.end(); ++it){
    _temp += (*it)->to_string();
    ++_counter;
    if(_counter < arity)
      _temp += ",";
  }
  return _temp + ")";
}

std::ostream & operator << (std::ostream & os, Vertex & v){
  os << "Symbol name: " << v.name << std::endl;
  os << "ID: " << v.id << std::endl;
  os << "Successors:" << std::endl;
  for(std::vector<Vertex*>::iterator it = v.successors.begin(); it != v.successors.end(); ++it)
    os << (*it)->to_string() << " ";
  return os;
}
