#ifndef _HORN_CLAUSE_
#define _HORN_CLAUSE_

#include <algorithm>
#include <list>
#include <z3++.h>
#include "UnionFind.h"
#include "Z3Subterms.h"

class HornClause {

  UnionFind &       uf;
  z3::context &     ctx;
  Z3Subterms &      subterms;
  z3::expr_vector   antecedent;
  z3::expr          consequent;
  PredList &        pred_list;
  bool              is_common_antecedent = true;
  unsigned          num_uncomm_antecedent = 0;

  void        normalize();
  void        orient();
  
public:
  HornClause(UnionFind &, z3::context &, Z3Subterms &, z3::expr_vector, z3::expr, PredList &);
  ~HornClause();
  
  bool                    checkTriviality();
  const z3::expr_vector & getAntecedent() const;
  const z3::expr &        getConsequent() const;
  bool                    isCommonAntecedent();
  bool                    isCommonConsequent();
  unsigned                numUncommAntecedent();

  static bool compareEquation(const z3::expr &, const z3::expr &);
  static bool compareTerm(const z3::expr &, const z3::expr &);
  
  friend bool operator <(const HornClause &, const HornClause &);
  friend bool operator >(const HornClause &, const HornClause &);
  
  friend std::ostream & operator << (std::ostream &, const HornClause &);
};

#endif
