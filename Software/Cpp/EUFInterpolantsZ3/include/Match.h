#ifndef _MATCH_
#define _MATCH_
#define DEBUG_DESTRUCTOR_MATCH 0

#include <iostream>
#include <vector>
#include <z3++.h>

// For historical reference
// Match1 : Uncommon term (indexed by its id) -> Positions of Horn Clauses
// Match2 : Uncommon equation (indexed by its id) -> Positions of Horn Clauses
class Match {
  std::vector<std::vector<unsigned> > m_vec;
public:
  Match();
  Match(std::vector<std::vector<unsigned> >);
  ~Match();
  unsigned size();
  void push_back(z3::expr const &, unsigned);
  std::vector<unsigned> operator [](unsigned);
  class iterator {
    Match * m_vec;
    unsigned m_index;
  public:
    iterator(Match *, unsigned);
    bool operator ==(iterator const &) const;
    bool operator !=(iterator const &) const;
    iterator & operator ++();
    std::vector<unsigned> operator *() const;
  };
  iterator begin() const;
  iterator end() const;
  friend std::ostream & operator << (std::ostream &, const Match &);
};

#endif
