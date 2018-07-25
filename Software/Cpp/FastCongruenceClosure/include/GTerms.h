#ifndef _GTERMS_
#define _GTERMS_

#include <iostream>
#include <algorithm>
#include <vector>
#include <set>
#include <vector>
#include "Vertex.h"
#include "UnionFind.h"
#include "z3++.h"
#include "z3.h"

extern bool debugVisit;
extern bool debugVisit2;

class GTerms{
 protected:
  std::vector<Vertex*> terms;
  UnionFind EC;
  std::set<std::string> symbolsToElim; 
  std::vector<std::pair<unsigned, unsigned> > equations, disEquations;
 private:
  void visit(Z3_context, Z3_ast, unsigned, unsigned &, std::set<std::string> &);
  void visit(Z3_context, Z3_ast, std::set<std::string> &);
  void exitf(const char *);
  void unreachable();
 public:
  GTerms(Z3_context, Z3_ast);
  GTerms(Z3_context, Z3_ast, std::set<std::string> &);
  GTerms(std::istream &);
  ~GTerms();
  Vertex * getTerm(unsigned);
  UnionFind & getEC();
  Vertex* find(Vertex*);
  void merge(Vertex*, Vertex*);
  std::ostream & print(std::ostream &);
};

#endif 
