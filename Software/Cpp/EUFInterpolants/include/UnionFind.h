#ifndef UNIONFIND_H
#define UNIONFIND_H

#include <vector>
#include "Node.h"

class UnionFind{
private:
  std::vector<unsigned> parent;
  unsigned numEquivalenceClasses;
public:
  UnionFind(unsigned);
  UnionFind();
  ~UnionFind();
  void merge(unsigned, unsigned);
  void link(unsigned, unsigned);
  void reset(unsigned);
  unsigned find(unsigned);
  unsigned size();
  friend std::ostream & operator << (std::ostream &, UnionFind &);
};

#endif
