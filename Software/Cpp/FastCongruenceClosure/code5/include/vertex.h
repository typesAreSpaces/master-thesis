#ifndef _VERTEX_
#define _VERTEX_

#include <iostream>
#include <vector>

class Vertex{
 private:
  static int totalNumVertex;
  std::string name;
  int id, arity;
  std::vector<Vertex*> successors;
 public:
  Vertex(std::string, int);
  Vertex();
  ~Vertex();
  void setName(std::string);
  void setArity(int);
  void addSuccessor(Vertex *);
  std::vector<Vertex*> & getSuccessors();
  std::string to_string();
  friend std::ostream & operator << (std::ostream &, Vertex &);
};

#endif
