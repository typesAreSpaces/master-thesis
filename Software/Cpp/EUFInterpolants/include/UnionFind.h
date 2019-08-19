#ifndef UNIONFIND_H
#define UNIONFIND_H

#include <iostream>
#include <vector>

class UnionFind{
private:
  std::vector<unsigned> representative;
  unsigned              num_equivalence_classes, length;
	
public:
  UnionFind(unsigned);
  UnionFind();
  ~UnionFind();
  void merge(unsigned, unsigned);
  void link(unsigned, unsigned);
  void reset(unsigned);
  unsigned find(unsigned);
  unsigned size();
  friend std::ostream & operator << (std::ostream &, const UnionFind &);
};

#endif
