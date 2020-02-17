#ifndef UNIONFIND_H
#define UNIONFIND_H

#include <iostream>
#include <vector>

class UnionFind{
private:
  std::vector<unsigned> representative;
public:
  UnionFind();
  UnionFind(unsigned);
  UnionFind(const std::vector<unsigned> &);
  ~UnionFind();
  void merge(unsigned, unsigned);
  void link(unsigned, unsigned);
  void reset(unsigned);
  unsigned find(unsigned);
  unsigned size() const;
  unsigned operator[] (unsigned) const;
  friend std::ostream & operator << (std::ostream &, const UnionFind &);
};

#endif
