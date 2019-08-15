#ifndef _VERTEX_
#define _VERTEX_

#include <iostream>
#include <vector>
#include "CircularList.h"

class Vertex{
 private:
  static unsigned          total_num_vertex;
  std::string             name;
  bool                     is_symbol_common;
  bool                     defined;
  unsigned                 id, arity;
  std::vector<Vertex*>    successors;
  CircularList<unsigned>   predecessors;
  void addPredecessor(unsigned);

 public:
  Vertex(std::string, unsigned);
  Vertex();
  ~Vertex();

  void setName(std::string);
  void setSymbolCommonQ(bool);
  void define();
  void setArity(unsigned);
  void addSuccessor(Vertex *);
  void mergePredecessors(Vertex *);
  
  static unsigned getTotalNumVertex();
  std::string getName();
  bool getSymbolCommonQ();
  unsigned getId();
  unsigned getArity();
  unsigned getLength();
  std::vector<Vertex*> & getSuccessors();
  CircularList<unsigned> * getPredecessors();
  std::string to_string();
  Vertex * getLeftChild();
  Vertex * getRightChild();
  
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
