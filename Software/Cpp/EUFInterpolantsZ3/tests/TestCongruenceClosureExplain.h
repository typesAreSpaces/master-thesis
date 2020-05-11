#ifndef _TEST_CONG_CLOSURE_EXPLAIN_
#define _TEST_CONG_CLOSURE_EXPLAIN_

#include <iostream>
#include <algorithm>
#include <z3++.h>
#include "Rename.h"
#include "EUFInterpolant.h"

class TestCongruenceClosureExplain {

  unsigned original_num_terms;

  z3::context &   ctx;
  Z3Subterms      subterms;
  z3::expr        contradiction;

  FSymPositions    fsym_positions;
  UnionFindExplain uf;
  PredList         pred_list;
  
  IdsToMerge ids_to_merge;

  CurryDeclarations curry_decl;  
  FactoryCurryNodes factory_curry_nodes;
  CongruenceClosureExplain cc;

  unsigned maxIdFromAssertions(z3::expr_vector const &);
  void init(z3::expr_vector const &);
  void initFormula(z3::expr const &);

  public:
  TestCongruenceClosureExplain(z3::expr_vector const &);
  bool testConsistency(z3::expr_vector const &, unsigned);
  void testExplanation(unsigned);
  friend std::ostream & operator << (std::ostream &, TestCongruenceClosureExplain &);

};

#endif
