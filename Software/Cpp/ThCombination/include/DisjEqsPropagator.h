#ifndef _DISJ_EQS_PROPAGATOR_
#define _DISJ_EQS_PROPAGATOR_

#include <z3++.h>
#include <deque>
#include <utility>

// Reference
// DFS approach:
// https://www.geeksforgeeks.org/make-combinations-size-k/

class DisjEqsPropagator {

  friend class ThCombInterpolator;

  typedef z3::expr_vector                            DisjEqs;
  typedef unsigned                                   CurrentIndex;
  typedef unsigned                                   CurrentSubsetSize;
  typedef std::pair<CurrentIndex, CurrentSubsetSize> DFSState;

  unsigned size, subset_size_query, ab_mixed_index;

  z3::expr_vector equalities;
  DisjEqs         current_disj_eqs;

  std::deque<DFSState> iterator_state;

  public:
  DisjEqsPropagator(z3::expr_vector const &);

  void    subsetSetup(unsigned);
  bool    hasNext();
  DisjEqs getCurrentDisjEqs() const;

  class iterator {

    DisjEqsPropagator * it;
    unsigned            index_block;

    public:
    iterator(DisjEqsPropagator *);

    void    init();
    bool    isLast();
    void    operator ++();
    z3::expr operator *() const;
  }; 

  iterator begin();
};

#endif
