#include "UnionFind.h"

UnionFind::UnionFind(unsigned n) : numEquivalenceClasses(n){
  parent.resize(n);
  for(unsigned i = 0; i < n; ++i)
    parent[i] = i;
}

UnionFind::UnionFind(){};

UnionFind::~UnionFind(){};

void UnionFind::merge(unsigned i, unsigned j){
  link(find(i), find(j));
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
  return numEquivalenceClasses;
}

std::ostream & UnionFind::print(std::ostream & os){
  unsigned i = 0;
  for(std::vector<unsigned>::iterator it = parent.begin(); it != parent.end(); ++it){
    os << "ID: " << i << " Parent: " << *it << std::endl;
    ++i;
  }
  return os;
}
