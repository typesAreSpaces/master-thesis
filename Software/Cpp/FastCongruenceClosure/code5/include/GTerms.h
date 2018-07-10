#ifndef _GTERMS_
#define _GTERMS_

#include <iostream>
#include <vector>
#include "vertex.h"
#include "unionfind.h"

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
  std::ostream & print(std::ostream &);
};

#endif 
