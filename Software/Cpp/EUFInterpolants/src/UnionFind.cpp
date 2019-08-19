#include "UnionFind.h"

UnionFind::UnionFind(unsigned n) : num_equivalence_classes(n), length(n){
  representative.resize(n);
  for(unsigned i = 0; i < n; ++i)
    representative[i] = i;
}

UnionFind::UnionFind(){};

UnionFind::~UnionFind(){};

void UnionFind::merge(unsigned x, unsigned y){
  representative[find(y)] = find(x);
  --num_equivalence_classes;  
}

void UnionFind::link(unsigned x, unsigned y){
  representative[y] = x;
  --num_equivalence_classes;
}

void UnionFind::reset(unsigned i){
  representative[i] = i;
}

unsigned UnionFind::find(unsigned x){
  if(x != representative[x])
    representative[x] = find(representative[x]);
  return representative[x];
}

unsigned UnionFind::size(){
  return length;
}

std::ostream & operator << (std::ostream & os, const UnionFind & uf){
  for(unsigned i = 0; i < uf.length; ++i){
    os << "ID: " << i;
    os << " Representative: " << uf.representative[i] << "\n";
    ++i;
  }
  return os;
}
