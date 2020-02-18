#ifndef _HORN_CLAUSE_
#define _HORN_CLAUSE_

#include <algorithm>

/* typedef std::pair<Term*, Term*> EquationTerm; */

/* class HornClause { */

/*   bool                      is_antecedent_common, is_consequent_common; */
/*   std::vector<EquationTerm> antecedent; */
/*   // The operator < heavily depends on this structure */
/*   UnionFind                 local_equiv_class; */
/*   EquationTerm              consequent; */
/*   void                      normalize(CongruenceClosure & cc); */
/*   void                      orient(); */
/*   static bool               compareEquations(const EquationTerm &, const EquationTerm &); */
  
/* public: */
/*   HornClause(CongruenceClosure &, */
/* 	     Term*, Term*, */
/* 	     bool);  */
/*   HornClause(CongruenceClosure &, */
/* 	     std::vector<EquationTerm> &, EquationTerm &); */
/*   ~HornClause(); */
  
/*   bool                        checkTriviality(UnionFind &); */

/*   bool                        getAntecedentCommon(); */
/*   bool                        getConsequentCommon(); */
/*   bool                        getMaximalConsequent(); */
  
/*   std::vector<EquationTerm> & getAntecedent(); */
/*   EquationTerm &              getConsequent(); */
/*   UnionFind &                 getLocalUF(); */
  
/*   friend bool                 operator <(HornClause &, HornClause &); */
/*   friend bool                 operator >(HornClause &, HornClause &); */
  
/*   friend std::ostream &       operator << (std::ostream &, const HornClause &); */
/* }; */

#endif
