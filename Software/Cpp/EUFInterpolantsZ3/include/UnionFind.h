#ifndef UNIONFIND_H
#define UNIONFIND_H

#include <iostream>
#include <vector>
#include <cassert>

class UnionFind {
  
  std::vector<unsigned> representative;
  std::vector<unsigned> rank;
  unsigned size;
  
public:
  UnionFind();
  UnionFind(unsigned [], unsigned);
  ~UnionFind();
  void merge(unsigned, unsigned);
  void link(unsigned, unsigned);
  unsigned find(unsigned);
  friend std::ostream & operator << (std::ostream &, const UnionFind &);
};

#endif
