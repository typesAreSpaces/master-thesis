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

std::size_t UnionFindExplain::hash_combine(unsigned t1, unsigned t2){
  std::size_t entry = hasher(t1);
  entry = hasher(t2) + 0x9e3779b9 + (entry<<6) + (entry>>2);
  return entry;
}

void UnionFindExplain::explainHelper(unsigned x, unsigned y,
				     ExplainEquations & explanations){

  std::cout << "Original " << x << " " << y << std::endl;
  if(x == y)
    return;
  
  unsigned oriented_step = 0, non_oriented_step = 0,
    original_x = x, original_y = y;
  std::size_t entry;
  
  while(x != forest[x]){  
    entry = hash_combine(x, forest[x]);
    x = forest[x];

    if(oriented_step < path[entry])
      oriented_step = path[entry];

    if(x == original_y){
      std::cout << "Oriented Step " << oriented_step << ": " << inserted_equations[oriented_step] << std::endl;
      explanations.push_back(inserted_equations[oriented_step]);
      explainHelper(original_x, inserted_equations[oriented_step].source, explanations);
      explainHelper(inserted_equations[oriented_step].target, original_y, explanations);
      return;
    }
  }
  
  while(y != forest[y]){ 
    entry = hash_combine(y, forest[y]);
    y = forest[y];
    
    if(non_oriented_step < path[entry])
      non_oriented_step = path[entry];

    if(y == original_x){
      std::cout << "Non oriented Step " << non_oriented_step << ": " << inserted_equations[non_oriented_step] << std::endl;
      explanations.push_back(inserted_equations[non_oriented_step]);
      explainHelper(y, inserted_equations[non_oriented_step].target, explanations);
      explainHelper(inserted_equations[non_oriented_step].source, original_y, explanations);
      return;
    }
  }

  if(x == y){
    if(oriented_step > non_oriented_step){
      std::cout << "Last Oriented Step " << oriented_step << ": " << inserted_equations[oriented_step] << std::endl;
      explanations.push_back(inserted_equations[oriented_step]);
      explainHelper(original_x, inserted_equations[oriented_step].source, explanations);
      explainHelper(records[oriented_step].target, original_y, explanations);
      return;
    }
    std::cout << "Last Non oriented Step " << non_oriented_step << ": " << inserted_equations[non_oriented_step] << std::endl;
    explanations.push_back(inserted_equations[non_oriented_step]);
    explainHelper(original_x, inserted_equations[non_oriented_step].target, explanations);
    explainHelper(inserted_equations[non_oriented_step].source, original_y, explanations);
    return;
  }
  
  return;
}

// The first argument becomes the new
// representative, always.
void UnionFindExplain::combine(unsigned target, unsigned source){
  assert(target < size && source < size);

  // Dealing with forest
  unsigned explain_source = forest[find(source)],
		  explain_target = forest[find(target)];
  records.emplace_back(explain_source, explain_target);
  inserted_equations.emplace_back(source, target);
  forest[find(source)] = explain_target;

  path[hash_combine(explain_source, explain_target)] = global_ticket++;
  
  representative[find(source)] = find(target);
  rank[find(target)] += rank[find(source)];
  
  return;
}

// The first argument becomes the new
// representative in forest, always.
void UnionFindExplain::merge(unsigned target, unsigned source){
  assert(target < size && source < size);
  
  // Dealing with forest 
  unsigned explain_source = forest[find(source)],
		  explain_target = forest[find(target)];
  records.emplace_back(explain_source, explain_target);
  inserted_equations.emplace_back(source, target);
  forest[find(source)] = explain_target;
  
  path[hash_combine(explain_source, explain_target)] = global_ticket++;
  
  // Dealing with representative
  link(find(target), find(source));
  
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

ExplainEquations UnionFindExplain::explain(unsigned x, unsigned y){
  ExplainEquations explanations;
  explainHelper(x, y, explanations);
  return explanations;
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
