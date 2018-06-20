#ifndef _UNIONFIND_
#define _UNIONFIND_

#include <cmath>
#include <vector>
#include <iostream>
#include <fstream>

extern bool debug;

// Data Structure for EUF

class UnionFind{
private:
  std::vector<int> parent, rank;
public:
  UnionFind(int);
  void _link(int, int);
  int _findSet(int);
  void _union(int, int);
};

#endif
