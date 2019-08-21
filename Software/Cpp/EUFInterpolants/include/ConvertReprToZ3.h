#ifndef _REPR_
#define _REPR_

#include "Term.h"
#include "HornClause.h"
#include "HornClauses.h"
#include "z3.h"
#include "Declarations.h"

class Converter {
 private:
  z3::context & ctx;
  z3::sort &    sort_A;
  std::vector<z3::func_decl>   funs;
  std::map<unsigned, unsigned> index;
 public:
  Converter(z3::context &, z3::sort &);
  z3::expr        convert(Term *);
  z3::expr        convert(const equality &);
  z3::expr        convert(const std::vector<equality> &);
  z3::expr_vector convert(const std::vector<Equation> &);
  z3::expr_vector convert(const std::vector<std::pair<Z3_ast, Z3_ast> > &);
  z3::expr        convert(HornClause *);
  z3::expr_vector convert(const std::vector<HornClause*> &);
  z3::expr        makeConjunction(const z3::expr_vector &);
  bool            areEqual(const z3::expr &, const z3::expr &);
  z3::expr        getAntecedent(const z3::expr &);
  z3::expr        getConsequent(const z3::expr &);
  z3::expr_vector extraSimplification(const z3::expr_vector &);
};

#endif
