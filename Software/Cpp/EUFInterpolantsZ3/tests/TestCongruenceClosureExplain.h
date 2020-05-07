#ifndef _TEST_CONG_CLOSURE_EXPLAIN_
#define _TEST_CONG_CLOSURE_EXPLAIN_

#include <iostream>
#include <algorithm>
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

  CurryDeclarations curry_decl;  
  FactoryCurryNodes factory_curry_nodes;
  CongruenceClosureExplain cc;

  void init(z3::expr const &);

  public:
  TestCongruenceClosureExplain(z3::expr const &);
  bool testConsistency(z3::expr const &);
  void testExplanation(unsigned);
  friend std::ostream & operator << (std::ostream &, TestCongruenceClosureExplain &);

};

#endif
