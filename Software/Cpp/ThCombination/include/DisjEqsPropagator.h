#ifndef _COMB_
#define _COMB_

#include <vector>
#include <deque>
#include <utility>
#include <z3++.h>

// Reference
// DFS approach:
// https://www.geeksforgeeks.org/make-combinations-size-k/

class DisjEqsPropagator {

  typedef std::vector<z3::expr>    Combination;
  typedef std::vector<Combination> Combinations;

  Combination equalities;

  unsigned     size;
  unsigned     subset_size_query;

  Combination  current_combination;
  Combinations result;

  std::deque<std::pair<unsigned, unsigned>> iterator_state;

  void makeCombinationsUtil(unsigned, unsigned);

  public:
  DisjEqsPropagator(Combination const &);

  Combinations makeCombinations(unsigned);

  void init(unsigned);
  bool next();
  Combination getCurrentCombination() const;

  class iterator {

    DisjEqsPropagator * it;
    unsigned            index_block;

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
