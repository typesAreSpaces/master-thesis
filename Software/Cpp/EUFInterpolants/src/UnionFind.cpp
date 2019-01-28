#include "UnionFind.h"

UnionFind::UnionFind(unsigned n) : num_equivalence_classes(n){
  parent.resize(n);
  for(unsigned i = 0; i < n; ++i)
    parent[i] = i;
}

UnionFind::UnionFind(){};

UnionFind::~UnionFind(){};

void UnionFind::merge(unsigned i, unsigned j){
  link(find(i), find(j));
  --num_equivalence_classes;
}

void UnionFind::link(unsigned i, unsigned j){
  parent[j] = i;
}

void UnionFind::reset(unsigned i){
  parent[i] = i;
}

unsigned UnionFind::find(unsigned i){
  if(i != parent[i])
    parent[i] = find(parent[i]);
  return parent[i];
}

unsigned UnionFind::size(){
  return num_equivalence_classes;
}

std::ostream & operator << (std::ostream & os, UnionFind & uf){
  unsigned i = 0;
  for(std::vector<unsigned>::iterator it = uf.parent.begin();
			it != uf.parent.end(); ++it){
    os << "ID: " << i << " Parent: " << *it << " ";
    ++i;
  }
  return os;
}
