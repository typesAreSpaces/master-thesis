#ifndef _TERMS_
#define _TERMS_

#include <iostream>
#include <vector>
#include <set>
#include <z3++.h>
#include "Term.h"
#include "UnionFind.h"

typedef std::pair<z3::expr, z3::expr> Equation;
typedef std::pair<z3::expr, z3::expr> Disequation;

class Terms {  
 public:
  Terms(z3::context &, const z3::expr &);
  Terms(z3::context &, const z3::expr &, const std::set<std::string> &);
  ~Terms();
  std::vector<Term*> & getTerms();
  void setEquivalenceClass(UnionFind &);
  UnionFind & getEquivalenceClass();
  UnionFind getDeepEquivalenceClass();
  Term * getOriginalTerm(unsigned);
  Term * getReprTerm (unsigned);
  Term * getReprTerm(Term*);
  void merge(Term*, Term*);
  void rotate(Term*, Term*);
  unsigned getRootNum();
  const std::set<std::string> & getSymbolsToElim();
  const std::vector<Equation> & getEquations();
  const std::vector<Disequation> & getDisequations();
  friend std::ostream & operator <<(std::ostream &, const Terms &);
 protected:
  z3::context &            ctx;
  unsigned                 root_num;
  std::vector<Equation>    equations;
  std::vector<Disequation> disequations;
  std::set<std::string>    symbols_to_elim;
  
  std::vector<Term*>       terms;
  UnionFind                equivalence_class;
 private:
  void exitf(const char *);
  void unreachable();
  void extractSymbolsAndTerms(const z3::expr &, std::set<std::string> &);
  void extractTerms(const z3::expr &);
  void removeSymbols(const z3::expr &, std::set<std::string> &);
};

#endif
