#include "UnionFindExplain.h"
#define DEBUG_DESTRUCTOR_UFE false

UnionFindExplain::UnionFindExplain() : size(0){
};

UnionFindExplain::UnionFindExplain(unsigned size) : representative(size, 0), rank(size, 1), size(size){
  for(unsigned i = 0; i < size; i++)
    representative[i] = i;
}

UnionFindExplain::UnionFindExplain(unsigned array[], unsigned size) :
  representative(array, array + size), rank(size, 1), size(size){
}

UnionFindExplain::UnionFindExplain(const UnionFindExplain & other) :
  representative(other.representative),
  rank(other.rank), size(other.size){
}

UnionFindExplain::~UnionFindExplain(){
#if DEBUG_DESTRUCTOR_UFE
  std::cout << "Done ~UnionFindExplain" << std::endl;
#endif
};

// The first argument becomes the new
// representative, always
void UnionFindExplain::combine(unsigned x, unsigned y){
  representative[find(y)] = find(x);
  rank[find(x)] += rank[find(y)];
  return;
}

void UnionFindExplain::merge(unsigned x, unsigned y){
  assert(x < size && y < size);
  link(find(x), find(y));
  return;
}

void UnionFindExplain::link(unsigned x, unsigned y){
  if(rank[x] > rank[y]){
    representative[y] = x;
    rank[x] += rank[y];
    return;
  }
  representative[x] = y;
  rank[y] += rank[x];
  return;
}

unsigned UnionFindExplain::find(unsigned x){
  assert(x < size);
  if(x != representative[x])
    representative[x] = find(representative[x]);
  return representative[x];
}

bool UnionFindExplain::greater(unsigned x, unsigned y){
  return rank[x] > rank[y];
}

std::vector<unsigned> UnionFindExplain::getEquivClass(unsigned x){
  std::vector<unsigned> ans;
  for(unsigned i = 0; i < size; i++)
    if(find(i) == x)
      ans.push_back(i);
  return ans;
}

void UnionFindExplain::increaseSize(unsigned sz){
  representative.resize(sz);
  rank.resize(sz);
  for(unsigned i = size; i < sz; i++){
    representative[i] = i;
    rank[i] = 1;
  }
  size = sz;
}

bool UnionFindExplain::operator ==(const UnionFindExplain & other){
  if(size != other.size)
    return false;
  for(unsigned i = 0; i < size; i++){
    if(representative[i] != other.representative[i])
      return false;
    if(rank[i] != other.rank[i])
      return false;
  }
  return true;
}

std::ostream & operator << (std::ostream & os, const UnionFindExplain & uf){
  for(unsigned i = 0; i < uf.representative.size(); ++i)
    os << "ID: " << i
       << " Representative: " << uf.representative[i]
       << " Rank:  " << uf.rank[i]
       << std::endl;
  os << "Size " << uf.size << std::endl;
  os << "(Remaider) The current representatives are not compressed.";
  return os;
}
