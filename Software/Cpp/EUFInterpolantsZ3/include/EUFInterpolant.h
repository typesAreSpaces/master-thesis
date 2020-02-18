#ifndef _EUF_INTERPOLANT_
#define _EUF_INTERPOLANT_

/* class EUFInterpolant { */

/*   CongruenceClosure auxiliar_closure; */
/*   CongruenceClosure original_closure; */
/*   Converter         cvt; */
/*   HornClauses       horn_clauses; */
/*   EquationTerm      contradiction; */
  
/*   void              eliminationOfUncommonFSyms(); */
/*   void              addNegativeHornClauses(); */
/*   z3::expr_vector   getUncommonTermsToElim(std::vector<HornClause*> &); */
/*   z3::expr_vector   exponentialElimination(z3::expr_vector &, z3::expr_vector &, z3::expr_vector &); */
/*   z3::expr_vector   substitutions(z3::expr &, z3::expr &, z3::expr_vector &); */
  
/*  public: */
/*   EUFInterpolant(const z3::expr &, const z3::sort &); */
/*   EUFInterpolant(const z3::expr &, const UncommonSymbols &, const z3::sort &); */
/*   ~EUFInterpolant(); */
/*   z3::expr                 buildInterpolant(); */
/*   std::vector<HornClause*> getHornClauses(); */
/*   friend std::ostream &    operator << (std::ostream &, EUFInterpolant &); */
/* }; */

#endif
