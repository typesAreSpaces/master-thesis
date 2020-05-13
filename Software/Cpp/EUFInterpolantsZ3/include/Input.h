#ifndef _INPUT_
#define _INPUT_

#include <map>
#include <z3++.h>
#include "Hornsat.h"
#include "CongruenceClosureExplain.h"
#include "CurryNode.h"

typedef std::map<std::string, std::vector<unsigned> > FSymPositions;

struct Input {
  
  unsigned original_num_terms;
  
  z3::context &   ctx;
  Z3Subterms      subterms;
  z3::expr        contradiction;
  z3::expr_vector disequalities;
  
  FSymPositions    fsym_positions;
  UnionFindExplain ufe;
  HornClauses      horn_clauses;

  IdsToMerge ids_to_merge;

  CurryDeclarations        curry_decl;  
  FactoryCurryNodes        factory_curry_nodes;
  CongruenceClosureExplain cc;

  unsigned maxIdFromAssertions(z3::expr_vector const &);
  void     init(z3::expr_vector const &);
  void     initFormula(z3::expr const &);
  void     disequalitiesToHCS();

  Input(z3::expr_vector const &);
  ~Input();
  z3::expr              repr(const z3::expr &);
  friend std::ostream & operator << (std::ostream &, Input const &);
};

#endif
