#ifndef _GTERMS_
#define _GTERMS_

#include <iostream>
#include <vector>
#include <map>
#include "z3++.h"
#include "Vertex.h"
#include "UnionFind.h"

class GTerms{
 private:
  std::vector<Vertex*> terms;
  UnionFind EC;
  void visit(Z3_context, Z3_ast);
 public:
  GTerms(Z3_context, Z3_ast);
  GTerms(std::istream &);
  ~GTerms();
  Vertex * getTerm(int);
  UnionFind & getEC();
  Vertex* find(Vertex*);
  void merge(Vertex*, Vertex*);
  std::ostream & print(std::ostream &);
};

#endif 
