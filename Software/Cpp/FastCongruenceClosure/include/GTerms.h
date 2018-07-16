#ifndef _GTERMS_
#define _GTERMS_

#include <iostream>
#include <vector>
#include "Vertex.h"
#include "UnionFind.h"

class GTerms{
 private:
  std::vector<Vertex*> terms;
  std::vector<Vertex*> additionalTerms;
  UnionFind EC;
 public:
  GTerms(std::istream &);
  ~GTerms();
  Vertex * getTerm(int);
  UnionFind & getEC();
  Vertex* find(Vertex*);
  void merge(Vertex*, Vertex*);
  std::ostream & print(std::ostream &);
};

#endif 