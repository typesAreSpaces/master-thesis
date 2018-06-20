#include "unionfind.hpp"

bool debug = false;

UnionFind::UnionFind(int n){
  for(int i = 0; i < n; ++i){
    parent.push_back(i);
    rank.push_back(0);
  }
}

void UnionFind::_link(int x, int y){
  if(rank[x] > rank[y])
    parent[y] = x;
  else{
    parent[x] = y;
    if(rank[x] == rank[y])
      ++rank[y];
  }
}

int UnionFind::_findSet(int x){
  if(parent[x] != x)
    parent[x] = _findSet(parent[x]);
  return parent[x];
}

void UnionFind::_union(int x, int y){
  _link(_findSet(x), _findSet(y));
}

