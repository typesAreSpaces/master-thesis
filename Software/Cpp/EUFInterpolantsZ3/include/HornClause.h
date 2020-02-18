#ifndef _HORN_CLAUSE_
#define _HORN_CLAUSE_

#include <z3++.h>

class HornClause {
  
  z3::expr_vector const & antecedent;
  z3::expr const &        consequent;
  // The operator < heavily depends on this structure
  // UnionFind       local_equiv_class;
  // void            normalize(CongruenceClosure & cc);
  // void            orient();
  
public:
  HornClause(z3::expr_vector const &, z3::expr const &);
  ~HornClause();
  
  // bool                        checkTriviality(UnionFind &);

  // bool                        getAntecedentCommon();
  // bool                        getConsequentCommon();
  // bool                        getMaximalConsequent();
  
  z3::expr_vector const & getAntecedent();
  z3::expr const &        getConsequent();
  // UnionFind &    getLocalUF();
  
  // friend bool    operator <(HornClause &, HornClause &);
  // friend bool    operator >(HornClause &, HornClause &);
  
  friend std::ostream & operator << (std::ostream &, const HornClause &);
};

#endif
