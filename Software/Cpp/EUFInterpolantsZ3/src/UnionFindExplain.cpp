#include "UnionFindExplain.h"
#define DEBUG_DESTRUCTOR_UFE false
#define DEBUG_EXPLAIN_OP false

UnionFindExplain::UnionFindExplain() :
  UnionFind(0), global_ticket(0){ 
};

UnionFindExplain::UnionFindExplain(unsigned size) :
  UnionFind(size), forest(size, 0), global_ticket(0){
  for(unsigned i = 0; i < size; i++)
    forest[i] = i;
}

UnionFindExplain::UnionFindExplain(const UnionFindExplain & other) :
  UnionFind(other), forest(other.forest),
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

unsigned UnionFindExplain::depth(unsigned x){
  unsigned aux = x, depth = 0;
  while(aux != forest[aux]){
    depth++;
    aux = forest[aux];
  }
  return depth;
}

unsigned UnionFindExplain::commonAncestor(unsigned x, unsigned y){
  unsigned depth_x = depth(x), depth_y = depth(y);
  unsigned aux_x = x, aux_y = y, diff_depth;
  if(depth_x >= depth_y){ 
    diff_depth = depth_x - depth_y;
    while(diff_depth--)
      aux_y = forest[aux_y];
    while(depth_x--){
      aux_x = forest[aux_x];
      aux_y = forest[aux_y];
      if(aux_x == aux_y)
	return aux_x;
    }
  }
  else{
    diff_depth = depth_y - depth_x;
    while(diff_depth--)
      aux_x = forest[aux_x];
    while(depth_y--){
      aux_x = forest[aux_x];
      aux_y = forest[aux_y];
      if(aux_x == aux_y)
	return aux_x;
    }
  }
  throw "The nodes are not in the same equivalence class";
}

void UnionFindExplain::explainHelper(Direction direction, unsigned last_step, unsigned original_x, unsigned original_y, ExplainEquations & explanations){
  explanations.push_back(&inserted_equations[last_step]);
  switch(direction){
  case ORIENTED:
    traverseExplain(original_x, inserted_equations[last_step].source, explanations);
    traverseExplain(inserted_equations[last_step].target, original_y, explanations);
    return;
  case REVERSED:
    traverseExplain(original_x, inserted_equations[last_step].target, explanations);
    traverseExplain(inserted_equations[last_step].source, original_y, explanations);
    return;
  }
}

void UnionFindExplain::traverseExplain(unsigned x, unsigned y, ExplainEquations & explanations){
#if DEBUG_EXPLAIN_OP
  std::cout << "Original " << x << " " << y << std::endl;
#endif  
  if(x == y)
    return;
  
  try{
    unsigned common_ancestor = commonAncestor(x, y);
    unsigned oriented_step = 0, reversed_step = 0, original_x = x, original_y = y;
    std::size_t entry = 0;
  
    while(x != common_ancestor){  
      entry = hash_combine(x, forest[x]);
      x = forest[x];
      if(oriented_step < path[entry])
	oriented_step = path[entry];
      if(x == original_y){
	explainHelper(ORIENTED, oriented_step, original_x, original_y, explanations);
	return;
      }
    }
    
    while(y != common_ancestor){ 
      entry = hash_combine(y, forest[y]);
      y = forest[y];
      if(reversed_step < path[entry])
	reversed_step = path[entry];
      if(y == original_x){
	explainHelper(REVERSED, reversed_step, original_x, original_y, explanations);
	return;
      }
    }
    
    if(x == y){
      if(oriented_step > reversed_step){
	explainHelper(ORIENTED, oriented_step, original_x, original_y, explanations);
	return;
      }
      explainHelper(REVERSED, reversed_step, original_x, original_y, explanations);
      return;
    }
  }
  catch(const char * e){
    explanations.clear();
    std::cout << e << std::endl;
  }
}

// The first argument becomes the new
// representative, always.
void UnionFindExplain::combine(unsigned target, unsigned source){
  assert(target < size && source < size);
  if(find(target) == find(source))
    return;

  // Dealing with forest
  unsigned explain_source = forest[find(source)], explain_target = forest[find(target)];
  inserted_equations.emplace_back(source, target);
  forest[find(source)] = explain_target;
  path[hash_combine(explain_source, explain_target)] = global_ticket++;
  
  UnionFind::combine(target, source); 
  return;
}

// The first argument becomes the new
// representative, always.
void UnionFindExplain::combine(unsigned target, unsigned source, const PendingElement * pe){
  assert(target < size && source < size);
  if(find(target) == find(source))
    return;

  // Dealing with forest
  unsigned explain_source = forest[find(source)], explain_target = forest[find(target)];
  inserted_equations.emplace_back(source, target, pe);
  forest[find(source)] = explain_target;
  path[hash_combine(explain_source, explain_target)] = global_ticket++;

  UnionFind::combine(target, source); 
  return;
}

// The first argument becomes the new
// representative in forest, always.
void UnionFindExplain::merge(unsigned target, unsigned source){
  assert(target < size && source < size);
  if(find(target) == find(source))
    return;
  
  // Dealing with forest 
  unsigned explain_source = forest[find(source)], explain_target = forest[find(target)];
  inserted_equations.emplace_back(source, target);
  forest[find(source)] = explain_target;  
  path[hash_combine(explain_source, explain_target)] = global_ticket++;
  
  UnionFind::merge(target, source);
  return;
}

// The first argument becomes the new
// representative in forest, always.
void UnionFindExplain::merge(unsigned target, unsigned source, const PendingElement * pe){
  assert(target < size && source < size);
  if(find(target) == find(source))
    return;
  
  // Dealing with forest 
  unsigned explain_source = forest[find(source)], explain_target = forest[find(target)];
  inserted_equations.emplace_back(source, target, pe);
  forest[find(source)] = explain_target;  
  path[hash_combine(explain_source, explain_target)] = global_ticket++;
  
  UnionFind::merge(target, source);
  return;
}

ExplainEquations UnionFindExplain::explain(unsigned x, unsigned y){
  ExplainEquations explanations;
  traverseExplain(x, y, explanations);
  return explanations;
}

std::ostream & UnionFindExplain::giveExplanation(std::ostream & os, unsigned x, unsigned y){
  os << "Explain " << x << ", " << y << std::endl;
  for(auto z : explain(x, y))
    os << *z << std::endl;
  return os;
}

void UnionFindExplain::resize(unsigned sz){
  representative.resize(sz);
  rank.resize(sz);
  forest.resize(sz);
  
  for(unsigned i = size; i < sz; i++){
    representative[i] = i;
    rank[i] = 1;
    forest[i] = i;
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
    if(forest[i] != other.forest[i])
      return false;
  }
  return true;
}

std::ostream & operator << (std::ostream & os, UnionFindExplain & uf){
  unsigned num_changes = 0;
  for(unsigned i = 0; i < uf.representative.size(); ++i){
    if(i != uf.find(i)) {
      num_changes++;
      os << "(Different)";
    }
    else
      os << "(Same)";
    os << "ID: " << i
       << " Forest: " << uf.forest[i]
       << " Representative " << uf.find(i)
       << std::endl;
  }
  os << "Size " << uf.size << std::endl;
  os << "Num changes: " << num_changes;
  return os;
}
