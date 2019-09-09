#ifndef _HORN_CLAUSE_
#define _HORN_CLAUSE_

#include <assert.h>
#include <vector>
#include <set>
#include <utility>
#include "Term.h"
#include "UnionFind.h"

typedef std::pair<Term*, Term*> EquationTerm;

class HornClause{	
 private:
  static UnionFind          global_UF;
  static bool               is_first_time;
  static std::vector<Term*> global_terms;
  UnionFind                 local_UF;	
  bool                      antecedent_boolean_value, consequent_boolean_value;
  std::vector<EquationTerm>     antecedent;
  EquationTerm                  consequent;
	
 public:
  HornClause(UnionFind &, std::vector<EquationTerm> &, EquationTerm &, std::vector<Term*> &);
  HornClause(UnionFind &, Term*, Term*, std::vector<Term*> &, bool);
  ~HornClause();
  void normalize();
  bool checkTriviality();
  bool getAntecedentValue();
  bool getConsequentValue();
  bool getMaximalConsequent();
  std::vector<EquationTerm> & getAntecedent();
  EquationTerm & getConsequent();
  UnionFind & getLocalUF();
  static UnionFind & getGlobalUF();
  Term * getTerm(unsigned);
  Term * getTerm(Term *);
  friend bool operator <(HornClause &, HornClause &);
  friend bool operator >(HornClause &, HornClause &);
  friend std::ostream & operator << (std::ostream &, HornClause &);
};

#endif
