#ifndef UNIONFIND_H
#define UNIONFIND_H

#include <vector>
#include "node.h"

class UnionFind{
private:
  std::vector<int> parent;
  int numEquivalenceClasses;
public:
  UnionFind(int);
  ~UnionFind();
  void merge(int, int);
  void link(int, int);
  int find(int);
  int size();
  std::ostream & print(std::ostream &);
};

#endif
