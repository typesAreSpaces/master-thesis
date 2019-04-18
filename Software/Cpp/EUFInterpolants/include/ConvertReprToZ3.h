#ifndef _REPR_
#define _REPR_

#include "Vertex.h"
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
  z3::expr        convert(Vertex *);
  z3::expr        convert(equality &);
  z3::expr        convert(std::vector<equality> &);
  z3::expr_vector convert(std::vector<std::pair<Z3_ast, Z3_ast> > &);
  z3::expr        convert(HornClause *);
  z3::expr_vector convert(std::vector<HornClause*> &);
  z3::expr        makeConjunction(z3::expr_vector &);
  bool            areEqual(z3::expr &, z3::expr &);
  z3::expr        getAntecedent(z3::expr &);
  z3::expr        getConsequent(z3::expr &);
};

#endif
