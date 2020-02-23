#include "UnionFind.h"

UnionFind::UnionFind(){
};

UnionFind::UnionFind(unsigned array[], unsigned size) :
  representative(array, array + size), rank(size, 0), size(size){
}

UnionFind::~UnionFind(){
};

// The first argument becomes the new
// representative, always
void UnionFind::merge(unsigned x, unsigned y){
  assert(x < size && y < size);
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
  assert(x < size);
  if(x != representative[x])
    representative[x] = find(representative[x]);
  return representative[x];
}

std::ostream & operator << (std::ostream & os, const UnionFind & uf){
  for(unsigned i = 0; i < uf.representative.size(); ++i)
    os << "ID: " << i
       << " Representative: " << uf.representative[i]
       << " Rank:  " << uf.rank[i]
       << std::endl;
  os << "(Remaider) The current representatives are not compressed.";
  return os;
}
