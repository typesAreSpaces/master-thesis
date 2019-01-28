#ifndef _TERMS_
#define _TERMS_

#include <iostream>
#include <algorithm>
#include <vector>
#include <set>
#include <vector>
#include "Vertex.h"
#include "UnionFind.h"
#include "z3.h"

class Terms{
 protected:
  unsigned                                root_num;
  std::vector<Vertex*>                    terms;
  std::set<std::string>                   symbols_to_elim; 
  std::vector<std::pair<Z3_ast, Z3_ast> > equations, disequations;
	UnionFind                               equivalence_class;
	
 private:
	void exitf(const char *);
  void unreachable();
  void traverse(Z3_context, Z3_ast,
						 unsigned, unsigned &, std::set<std::string> &);
  void traverse(Z3_context, Z3_ast,
						 std::set<std::string> &);
  
 public:
  Terms(Z3_context, Z3_ast);
  Terms(Z3_context, Z3_ast, std::set<std::string> &);
  Terms(std::istream &);
  ~Terms();
  std::vector<Vertex*> & getTerms();
  UnionFind & getEquivalenceClass();
	Vertex * getOriginalVertex(unsigned);
	Vertex * getVertex(unsigned);
  Vertex * getVertex(Vertex*);
  void merge(Vertex*, Vertex*);
  void rotate(Vertex*, Vertex*);
  unsigned getRootNum();
  std::set<std::string> & getSymbolsToElim();
	std::vector<std::pair<Z3_ast, Z3_ast> > & getEquations();
	std::vector<std::pair<Z3_ast, Z3_ast> > & getDisequations();
	friend std::ostream & operator <<(std::ostream &, Terms &);
};

#endif
