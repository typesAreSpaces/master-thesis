#ifndef _REPR_
#define _REPR_
#define notInSet(y, x) x.find(y) == x.end()

#include <map>
#include "Term.h"
#include "Terms.h"
#include "HornClause.h"

class Converter {
 public:
  Converter(z3::context &, const z3::sort &);
  z3::expr              convert(Term *);
  z3::expr              convert(const EquationTerm &);
  z3::expr              convert(const std::vector<EquationTerm> &);
  z3::expr_vector       convert(const std::vector<Equation> &);
  z3::expr              convert(HornClause *);
  z3::expr_vector       convert(const std::vector<HornClause*> &);
  z3::expr              makeConjunction(const z3::expr_vector &);
  z3::expr              getAntecedent(const z3::expr &);
  z3::expr              getConsequent(const z3::expr &);
  z3::expr_vector       extraSimplification(const z3::expr_vector &);
  z3::expr_vector       removeUncommonTerms(const z3::expr_vector &);
  std::set<std::string> getSymbols(const z3::expr &);
  void                  auxiliarGetSymbols(const z3::expr &, std::set<std::string> &);
 private:
  z3::context &    ctx;
  const z3::sort & sort_A;
};

#endif
