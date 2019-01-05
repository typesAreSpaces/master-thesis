#ifndef _VERTEX_
#define _VERTEX_

#include <iostream>
#include <vector>
#include "CircularList.h"

class Vertex{
 private:
  static unsigned totalNumVertex;
  std::string name;
  bool symbolCommonQ;
	bool defined;
  unsigned id, arity;
  std::vector<Vertex*> successors;
  CircularList<unsigned> predecessors;
  void addPredecessor(unsigned);
 public:
  Vertex(std::string, unsigned);
  Vertex();
  ~Vertex();
  std::string getName();
  void setName(std::string);
  unsigned getArity();
  void setArity(unsigned);
  void addSuccessor(Vertex *);
  std::vector<Vertex*> & getSuccessors();
  CircularList<unsigned> * getPredecessors();
  unsigned getId();
  unsigned getLength();
  bool getSymbolCommonQ();
  void setSymbolCommonQ(bool);
  void mergePredecessors(Vertex *);
  Vertex * getRightChild();
  Vertex * getLeftChild();
  std::string to_string();
  std::ostream & ss (std::ostream &);
  static unsigned getTotalNumVertex();
  friend std::ostream & operator << (std::ostream &, Vertex &);
  friend bool operator ==(const Vertex &, const Vertex &);
  friend bool operator !=(const Vertex &, const Vertex &);
  friend bool operator <(const Vertex &, const Vertex &);
  friend bool operator <=(const Vertex &, const Vertex &);
  friend bool operator >(const Vertex &, const Vertex &);
  friend bool operator >=(const Vertex &, const Vertex &);
	void define();
};

#endif
