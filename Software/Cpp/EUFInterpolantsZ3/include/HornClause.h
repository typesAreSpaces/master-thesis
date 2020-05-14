#ifndef _HORN_CLAUSE_
#define _HORN_CLAUSE_

#include <algorithm>
#include <list>
#include <z3++.h>
#include "UnionFindExplain.h"
#include "Z3Subterms.h"
#include "Util.h"

class HornClause {

  z3::context &   ctx;
  z3::expr_vector antecedent;
  z3::expr        consequent;
  bool            is_common_antecedent;
  unsigned        num_uncomm_antecedent;

  void normalize(UnionFindExplain &);
  void orient();
  
public:
  HornClause(z3::context &, z3::expr_vector, z3::expr, UnionFindExplain &);
  ~HornClause();
  
  bool                    checkTriviality(UnionFindExplain &);
  const z3::expr_vector & getAntecedent()       const;
  const z3::expr &        getConsequent()       const;
  bool                    isCommonAntecedent()  const;
  bool                    isCommonConsequent()  const;
  unsigned                numUncommAntecedent() const;

  friend bool operator <(const HornClause &, const HornClause &);
  friend bool operator >(const HornClause &, const HornClause &);
  
  friend std::ostream & operator << (std::ostream &, const HornClause &);
};

#endif
