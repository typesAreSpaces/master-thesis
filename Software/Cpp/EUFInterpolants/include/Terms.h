#ifndef _TERMS_
#define _TERMS_

#include <iostream>
#include <algorithm>
#include <vector>
#include <set>
#include <vector>
#include "Term.h"
#include "UnionFind.h"
#include "z3.h"
#include "z3++.h"

class Terms{
 protected:
  unsigned                                root_num;
  std::vector<Term*>                      terms;
  std::set<std::string>                   symbols_to_elim; 
  std::vector<std::pair<Z3_ast, Z3_ast> > equations, disequations;
  UnionFind                               equivalence_class;
	
 private:
  void exitf(const char *);
  void unreachable();
  void extractSymbolsAndTerms(Z3_context, Z3_ast, std::set<std::string> &);
  void extractSymbols(Z3_context, Z3_ast, std::set<std::string> &);
  
 public:
  Terms(Z3_context, Z3_ast);
  Terms(Z3_context, Z3_ast, const std::set<std::string> &);
  ~Terms();
  std::vector<Term*> & getTerms();
  UnionFind & getEquivalenceClass();
  Term * getOriginalTerm(unsigned);
  Term * getReprTerm(unsigned);
  Term * getReprTerm(Term*);
  void merge(Term*, Term*);
  void rotate(Term*, Term*);
  unsigned getRootNum();
  const std::set<std::string> & getSymbolsToElim();
  const std::vector<std::pair<Z3_ast, Z3_ast> > & getEquations();
  const std::vector<std::pair<Z3_ast, Z3_ast> > & getDisequations();
  friend std::ostream & operator <<(std::ostream &, const Terms &);
};

#endif
