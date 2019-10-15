#ifndef _REPR_
#define _REPR_
#define InSet(y, x) x.find(y) == x.end()

#include <map>
#include "Term.h"
#include "Terms.h"
#include "HornClause.h"

class Converter {
 public:
  Converter(z3::context &, const z3::sort &);
  z3::expr        convert(Term *);
  z3::expr        convert(const EquationTerm &);
  z3::expr        convert(const std::vector<EquationTerm> &);
  z3::expr_vector convert(const std::vector<Equation> &);
  z3::expr        convert(HornClause *);
  z3::expr_vector convert(const std::vector<HornClause*> &);
  z3::expr        makeConjunction(const z3::expr_vector &);
  bool            areEqual(const z3::expr &, const z3::expr &);
  z3::expr        getAntecedent(const z3::expr &);
  z3::expr        getConsequent(const z3::expr &);
  z3::expr_vector extraSimplification(const z3::expr_vector &);
 private:
  z3::context &    ctx;
  const z3::sort & sort_A;
};

#endif
