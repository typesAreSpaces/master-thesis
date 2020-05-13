#ifndef _HORN_CLAUSE_
#define _HORN_CLAUSE_

#include <algorithm>
#include <list>
#include <z3++.h>
#include "UnionFindExplain.h"
#include "Z3Subterms.h"

class HornClause {

  z3::context &   ctx;
  z3::expr_vector antecedent;
  z3::expr        consequent;
  bool            is_common_antecedent = true;
  unsigned        num_uncomm_antecedent = 0;

  void normalize(UnionFindExplain &);
  void orient();
  
public:
  HornClause(UnionFindExplain &, z3::context &, z3::expr_vector, z3::expr);
  ~HornClause();
  
  bool                    checkTriviality(UnionFindExplain &);
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
