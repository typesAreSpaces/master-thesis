#ifndef _HORN_CLAUSE_
#define _HORN_CLAUSE_

#include <algorithm>
#include <z3++.h>
#include "UnionFind.h"

class HornClause {

  UnionFind &       uf;
  z3::expr_vector & antecedent;
  z3::expr &        consequent;

  bool            checkTriviality();
  static bool     compareEquation(const z3::expr &, const z3::expr &);
  static bool     compareTerm(const z3::expr &, const z3::expr &);
  void            normalize();
  void            orient();
  
public:
  HornClause(UnionFind &, z3::expr_vector &, z3::expr &);
  ~HornClause();
  
  z3::expr_vector & getAntecedent();
  z3::expr &        getConsequent();
  
  friend bool operator <(const HornClause &, const HornClause &);
  friend bool operator >(const HornClause &, const HornClause &);
  
  friend std::ostream & operator << (std::ostream &, const HornClause &);
};

#endif
