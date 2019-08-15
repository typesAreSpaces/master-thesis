#ifndef _VERTEX_
#define _VERTEX_

#include <iostream>
#include <vector>
#include "CircularList.h"

class Vertex{
 private:
  static unsigned        total_num_vertex;
  std::string            name;
  bool                   is_symbol_common;
  bool                   defined;
  unsigned               id, arity;
  std::vector<Vertex*>   successors;
  CircularList<unsigned> predecessors;
  void addPredecessor(unsigned);

 public:
  Vertex(std::string, unsigned);
  Vertex();
  ~Vertex();
  void setName(std::string);
  void setArity(unsigned);
  void setSymbolCommonQ(bool);
  void addSuccessor(Vertex *);
  void mergePredecessors(Vertex *);
  void define();
  std::string getName();
  unsigned getArity();
  unsigned getId();
  unsigned getLength();
  static unsigned getTotalNumVertex();
  bool getSymbolCommonQ();
  std::string to_string();
  std::vector<Vertex*> & getSuccessors();
  CircularList<unsigned> * getPredecessors();
  Vertex * getRightChild();
  Vertex * getLeftChild();
  std::ostream & functionPrettyPrint (std::ostream &);
  friend std::ostream & operator << (std::ostream &, Vertex &);
  friend bool operator ==(const Vertex &, const Vertex &);
  friend bool operator !=(const Vertex &, const Vertex &);
  friend bool operator <(const Vertex &, const Vertex &);
  friend bool operator <=(const Vertex &, const Vertex &);
  friend bool operator >(const Vertex &, const Vertex &);
  friend bool operator >=(const Vertex &, const Vertex &);
};

#endif
