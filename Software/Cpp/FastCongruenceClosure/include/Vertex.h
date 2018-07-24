#ifndef _VERTEX_
#define _VERTEX_

#include <iostream>
#include <vector>
#include <CircularList.h>
#include <CircularList.cpp>

class Vertex{
 private:
  static unsigned totalNumVertex;
  std::string name;
  unsigned id, arity;
  std::vector<Vertex*> successors;
  CircularList<unsigned> predecessors;
  void addPredecessor(unsigned);
 public:
  Vertex(std::string, unsigned);
  Vertex();
  ~Vertex();
  void setName(std::string);
  void setArity(unsigned);
  void addSuccessor(Vertex *);
  std::vector<Vertex*> & getSuccessors();
  CircularList<unsigned> * getPredecessors();
  unsigned getId();
  unsigned getArity();
  std::string getName();
  unsigned getLength();
  void mergePredecessors(Vertex *);
  std::string to_string();
  std::ostream & ss (std::ostream &);
  static unsigned getTotalNumVertex();
  friend std::ostream & operator << (std::ostream &, Vertex &);
};

#endif
