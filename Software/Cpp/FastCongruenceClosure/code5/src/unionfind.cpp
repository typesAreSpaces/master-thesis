#include "unionfind.h"

UnionFind::UnionFind(int n) : numEquivalenceClasses(n){
  parent.resize(n);
  for(int i = 0; i < n; ++i)
    parent[i] = i;
}

UnionFind::UnionFind(){};

UnionFind::~UnionFind(){};

void UnionFind::merge(int i, int j){
  link(find(i), find(j));
}

void UnionFind::link(int i, int j){
  parent[j] = i;
}

int UnionFind::find(int i){
  if(i != parent[i])
    parent[i] = find(parent[i]);
  return parent[i];
}

int UnionFind::size(){
  return numEquivalenceClasses;
}

std::ostream & UnionFind::print(std::ostream & os){
  int i = 0;
  for(std::vector<int>::iterator it = parent.begin(); it != parent.end(); ++it){
    os << "ID: " << i << " Parent: " << *it << std::endl;
    ++i;
  }
  return os;
}
