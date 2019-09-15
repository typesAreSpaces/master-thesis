#include "UnionFind.h"

UnionFind::UnionFind(){};

UnionFind::UnionFind(unsigned n){
  representative.resize(n);
  for(unsigned i = 0; i < n; ++i)
    representative[i] = i;
}

UnionFind::UnionFind(std::vector<unsigned> values):
  representative(values){};

UnionFind::~UnionFind(){
};

void UnionFind::merge(unsigned x, unsigned y){
  representative[find(y)] = find(x);
}

void UnionFind::link(unsigned x, unsigned y){
  representative[y] = x;
}

void UnionFind::reset(unsigned i){
  representative[i] = i;
}

unsigned UnionFind::find(unsigned x){  
  if(x != representative[x])
    representative[x] = find(representative[x]);
  return representative[x];
}

unsigned UnionFind::size() const {
  return representative.size();
}

unsigned UnionFind::operator[](unsigned index) const {
  return representative[index];
}

std::ostream & operator << (std::ostream & os, const UnionFind & uf){
  for(unsigned i = 0; i < uf.representative.size(); ++i){
    os << "ID: " << i;
    os << " Representative: " << uf.representative[i] << "\n";
  }
  return os;
}
