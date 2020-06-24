#ifndef _COMB_
#define _COMB_

#include <vector>
#include <z3++.h>

// Reference
// DFS approach:
// https://www.geeksforgeeks.org/make-combinations-size-k/

class DisjEqsPropagator {

  typedef std::vector<z3::expr>    Combination;
  typedef std::vector<Combination> Combinations;

  Combination equalities;

  unsigned     size;
  Combination  current_combination;
  Combinations result;

  void makeCombinationsUtil(unsigned, unsigned);

  public:
  DisjEqsPropagator(Combination const &);

  Combinations makeCombinations(unsigned);

  class iterator {

    DisjEqsPropagator * it;
    unsigned            index_block;

    DisjEqsPropagator::Combinations           current_block;
    DisjEqsPropagator::Combinations::iterator current_disj;

    public:
    iterator(DisjEqsPropagator *);

    void init();
    void last();
    bool isLast();
    void next();
    Combination operator * () const;
  }; 

  iterator begin();
  iterator end();
};

#endif
