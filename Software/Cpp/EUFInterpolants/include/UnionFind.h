#ifndef UNIONFIND_H
#define UNIONFIND_H

#include <iostream>
#include <vector>

class UnionFind{
public:
  UnionFind();
  UnionFind(unsigned);
  UnionFind(std::vector<unsigned>);
  ~UnionFind();
  void merge(unsigned, unsigned);
  void link(unsigned, unsigned);
  void reset(unsigned);
  unsigned find(unsigned);
  unsigned size();
  unsigned operator[] (unsigned) const;
  friend std::ostream & operator << (std::ostream &, const UnionFind &);
 private:
  std::vector<unsigned> representative;
};

#endif
