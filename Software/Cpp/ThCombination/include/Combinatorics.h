#ifndef _COMB_
#define _COMB_

#include <vector>
#include <z3++.h>

// Reference
// DFS approach:
// https://www.geeksforgeeks.org/make-combinations-size-k/

class Combinatorics {

  typedef std::vector<z3::expr>    Combination;
  typedef std::vector<Combination> Combinations;

  Combination const & elements;

  unsigned     size;
  Combination  current_combination;
  Combinations result;

  void makeCombinationsUtil(unsigned, unsigned);

  public:
  Combinatorics(Combination const &);

  Combinations makeCombinations(unsigned);
};

#endif
