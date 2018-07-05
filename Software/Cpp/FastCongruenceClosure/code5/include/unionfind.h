#ifndef UNIONFIND_H
#define UNIONFIND_H

#include <vector>
#include "node.h"
#include "LinkedList.h"
#include "LinkedList.cpp"
#include "Circular.h"
#include "CircularList.cpp"

class UnionFind{
private:
  std::vector<int> parent, rank;
  std::vector<CircularList<int> > preds;
  int length;
public:
  UnionFind(int);
  void setPreds(LinkedList &);
  void addPred(int x, int y){
    preds[x].add(y);
  }
  void merge(int x, int y){
    link(find(x), find(y));
    --length;
  }
  void link(int x, int y){
    parent[y] = x;
  }
  int find(int x){
    if(parent[x] != x)
      parent[x] = find(parent[x]);
    return parent[x];
  }
  CircularList<int> list(int x){
    return preds[x];
  }
  int getRank(int x){
    return rank[find(x)];
  }
  int size(){
    return length;
  }
};

#endif
