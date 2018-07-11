#ifndef _VERTEX_
#define _VERTEX_

#include <iostream>
#include <vector>
#include <CircularList.h>
#include <CircularList.cpp>

class Vertex{
 private:
  static int totalNumVertex;
  std::string name;
  int id, arity;
  std::vector<Vertex*> successors;
  CircularList<int> predecessors;
  void addPredecessor(int);
 public:
  Vertex(std::string, int);
  Vertex();
  ~Vertex();
  void setName(std::string);
  void setArity(int);
  void addSuccessor(Vertex *);
  std::vector<Vertex*> & getSuccessors();
  CircularList<int> * getPredecessors();
  int getId();
  int getArity();
  std::string getName();
  int getLength();
  void mergePredecessors(Vertex *);
  std::string to_string();
  static int getTotalNumVertex();
  friend std::ostream & operator << (std::ostream &, Vertex &);
};

#endif
