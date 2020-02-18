#ifndef UNIONFIND_H
#define UNIONFIND_H

#include <iostream>
#include <vector>

class UnionFind {
  
  std::vector<unsigned> representative;
  std::vector<unsigned> rank;
  
public:
  UnionFind();
  UnionFind(unsigned [], unsigned);
  ~UnionFind();
  void merge(unsigned, unsigned);
  void link(unsigned, unsigned);
  unsigned find(unsigned);
  friend std::ostream & operator << (std::ostream &, UnionFind &);
};

#endif
