#include "UnionFindExplain.h"
#define DEBUG_DESTRUCTOR_UFE false

UnionFindExplain::UnionFindExplain() :
  size(0), global_ticket(0){ 
};

UnionFindExplain::UnionFindExplain(unsigned size) :
  representative(size, 0), rank(size, 1),
  forest(size, 0), size(size), global_ticket(0){

  for(unsigned i = 0; i < size; i++){
    representative[i] = i;
    forest[i] = i;
  }
}

UnionFindExplain::UnionFindExplain(const UnionFindExplain & other) :
  representative(other.representative),
  rank(other.rank), forest(other.forest),
  records(other.records), size(other.size),
  global_ticket(other.global_ticket){
}

UnionFindExplain::~UnionFindExplain(){
#if DEBUG_DESTRUCTOR_UFE
  std::cout << "Done ~UnionFindExplain" << std::endl;
#endif
};

// The first argument becomes the new
// representative, always.
// i.e.                         target---   source---
//                                      |           |
//                                      v           v 
void UnionFindExplain::combine(unsigned x, unsigned y){
  assert(x < size && y < size);

  // Dealing with forest
  unsigned explain_y = forest[find(y)], explain_x = forest[find(x)];
  records.emplace_back(explain_y, explain_x);
  forest[find(y)] = forest[find(x)];

  std::size_t entry = hasher(explain_y);
  entry = hasher(explain_x) + 0x9e3779b9 + (entry<<6) + (entry>>2);
  path[entry] = global_ticket++;
  
  representative[find(y)] = find(x);
  rank[find(x)] += rank[find(y)];
  
  return;
}

// The first argument becomes the new
// representative in forest, always.
// i.e.                       target---   source---
//                                    |           |
//                                    v           v 
void UnionFindExplain::merge(unsigned x, unsigned y){
  assert(x < size && y < size);
  
  // Dealing with forest 
  unsigned explain_y = forest[find(y)], explain_x = forest[find(x)];
  records.emplace_back(explain_y, explain_x);
  forest[find(y)] = forest[find(x)];
  
  std::size_t entry = hasher(explain_y);
  entry = hasher(explain_x) + 0x9e3779b9 + (entry<<6) + (entry>>2);
  path[entry] = global_ticket++;
  
  // Dealing with representative
  link(find(x), find(y));
  
  return;
}

void UnionFindExplain::link(unsigned x, unsigned y){
  if(rank[x] >= rank[y]){
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

void UnionFindExplain::explain(unsigned x, unsigned y){

  std::cout << "Original " << x << " " << y << std::endl;

  if(x == y)
    return;
  
  unsigned step = 0, original_x = x, original_y = y;
  bool oriented = true;
  while(x != forest[x]){
    std::size_t entry = hasher(x);
    entry = hasher(forest[x]) + 0x9e3779b9 + (entry<<6) + (entry>>2);
    x = forest[x];

    std::cout << records[path[entry]] << std::endl;

    if(step < path[entry])
      step = path[entry];
  }

  std::cout << "reverse the following" << std::endl;
  
  while(y != forest[y]){  
    std::size_t entry = hasher(y);
    entry = hasher(forest[y]) + 0x9e3779b9 + (entry<<6) + (entry>>2);
    y = forest[y];
    
    std::cout << records[path[entry]] << std::endl;
    
    if(step < path[entry]){
      step = path[entry];
      oriented = false;
    }
  }
  std::cout << original_x << " " << original_y << std::endl;
  std::cout << step << " (" << records[step] << ") " << (oriented == true) << std::endl;

  if(oriented){
    std::cout << "It was oriented" << std::endl;
    explain(original_x, records[step].source);
    explain(records[step].target, original_y);
    return;
  }
  std::cout << "It wasn't oriented" << std::endl;
  explain(original_x, records[step].target);
  explain(records[step].source, original_y);
  return;
}

bool UnionFindExplain::greater(unsigned x, unsigned y){
  return rank[x] > rank[y];
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
       << " Forest: " << uf.forest[i]
       << " Rank:  " << uf.rank[i]
       << std::endl;
  os << "Size " << uf.size << std::endl;
  os << "(Remaider) The current representatives are not compressed.";
  return os;
}
