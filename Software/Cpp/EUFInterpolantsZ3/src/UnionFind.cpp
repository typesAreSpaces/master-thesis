#include "UnionFind.h"

UnionFind::UnionFind(){
};

UnionFind::UnionFind(unsigned array[], unsigned size) :
  representative(array, array + size), rank(size, 0){
}

UnionFind::~UnionFind(){
};

// The first argument becomes the new
// representative, always
void UnionFind::merge(unsigned x, unsigned y){
  link(find(x), find(y));
  return;
}

void UnionFind::link(unsigned x, unsigned y){
  if(rank[x] > rank[y]){
    representative[y] = x;
    return;
  }
  representative[x] = y;
  if(rank[x] == rank[y])
    rank[y]++;
  return;
}

unsigned UnionFind::find(unsigned x){  
  if(x != representative[x])
    representative[x] = find(representative[x]);
  return representative[x];
}

std::ostream & operator << (std::ostream & os, UnionFind & uf){
  for(unsigned i = 0; i < uf.representative.size(); ++i)
    os << "ID: " << i
       << " Representative: " << uf.find(i) << std::endl;
  return os;
}
