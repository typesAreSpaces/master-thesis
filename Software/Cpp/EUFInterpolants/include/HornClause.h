#ifndef _HORN_CLAUSE_
#define _HORN_CLAUSE_

#include <assert.h>
#include <vector>
#include <set>
#include <utility>
#include "Term.h"
#include "CongruenceClosure.h"

typedef std::pair<Term*, Term*> EquationTerm;

class HornClause {
 public:
  HornClause(CongruenceClosure &,
	     Term*, Term*,
	     bool); 
  HornClause(CongruenceClosure &,
	     std::vector<EquationTerm> &, EquationTerm &);
  ~HornClause();
  
  void                        normalize(CongruenceClosure &);
  bool                        checkTriviality(CongruenceClosure &);

  bool                        getAntecedentCommon();
  bool                        getConsequentCommon();
  bool                        getMaximalConsequent();
  
  std::vector<EquationTerm> & getAntecedent();
  EquationTerm &              getConsequent();
  
  friend bool                 operator <(HornClause &, HornClause &);
  friend bool                 operator >(HornClause &, HornClause &);
  friend std::ostream &       operator << (std::ostream &, const HornClause &);
  
 private:
  bool                      is_antecedent_common, is_consequent_common;
  std::vector<EquationTerm> antecedent;
  EquationTerm              consequent;
};

#endif
