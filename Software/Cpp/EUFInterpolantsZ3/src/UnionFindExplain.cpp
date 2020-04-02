#include "UnionFindExplain.h"
#define DEBUG_DESTRUCTOR_UFE false
#define DEBUG_EXPLAIN_OP false

UnionFindExplain::UnionFindExplain() :
  UnionFind(0) { 
  };

UnionFindExplain::UnionFindExplain(unsigned size) :
  UnionFind(size), proof_forest(size, 0){
    for(unsigned i = 0; i < size; i++)
      proof_forest[i] = i;
  }

UnionFindExplain::UnionFindExplain(const UnionFindExplain & other) :
  UnionFind(other), proof_forest(other.proof_forest) {
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

unsigned UnionFindExplain::getRootProofForest(unsigned x){
  unsigned aux = x;
  while(aux != proof_forest[aux])
    aux = proof_forest[aux];
  return aux;
}

unsigned UnionFindExplain::depth(unsigned x){
  unsigned aux = x, depth = 0;
  while(aux != proof_forest[aux]){
    depth++;
    aux = proof_forest[aux];
  }
  return depth;
}

unsigned UnionFindExplain::commonAncestor(unsigned x, unsigned y) {
  if(find(x) == find(y)){
    unsigned depth_x = depth(x), depth_y = depth(y);
    unsigned aux_x = x, aux_y = y, diff_depth;
    if(depth_x >= depth_y){ 
      diff_depth = depth_x - depth_y;
      while(diff_depth--)
        aux_x = proof_forest[aux_x];
      while(aux_x != aux_y){
        aux_x = proof_forest[aux_x];
        aux_y = proof_forest[aux_y];
      }
      return aux_x;
    }
    else{
      diff_depth = depth_y - depth_x;
      while(diff_depth--)
        aux_y = proof_forest[aux_y];
      while(aux_x != aux_y){
        aux_x = proof_forest[aux_x];
        aux_y = proof_forest[aux_y];
      }
      return aux_x;
    }
  }
  throw "The nodes are not in the same equivalence class";
}

void UnionFindExplain::explainAlongPath(unsigned a, unsigned c, ExplainEquations & explanations) {
  while(a != c){
    explanations.push_back(ExplainEquation(a, proof_forest[a]));
    a = proof_forest[a];
  }
} 

ExplainEquations UnionFindExplain::explain(unsigned x, unsigned y){
  ExplainEquations explanations;
  try {
    unsigned c = commonAncestor(x, y);
    explainAlongPath(x, c, explanations);
    explainAlongPath(y, c, explanations);
    return explanations;
  }
  catch(...){
    return explanations;
  } 
}

// The first argument becomes the new
// representative, always.
void UnionFindExplain::combine(unsigned target, unsigned source){
  assert(target < size && source < size);
  if(find(target) == find(source))
    return;
  
  // ---------------------------------------------------------------------
  // Reverse the edges between the source
  // and its representative
  std::list<ExplainEquation> stack;
  unsigned aux_source = source;
  while(aux_source != proof_forest[aux_source]) {
    stack.push_back(ExplainEquation(aux_source, proof_forest[aux_source]));
    aux_source = proof_forest[aux_source];
  }
  while(!stack.empty()) {
    const auto element = stack.back();
    stack.pop_back();
    proof_forest[element.target] = element.source;
    if(stack.empty())
      proof_forest[element.source] = element.source;
  }
  // ---------------------------------------------------------------------

  proof_forest[source] = target;

  UnionFind::combine(target, source); 
  return;
}

// The first argument becomes the new
// representative in the proof_forest, always.
void UnionFindExplain::merge(unsigned target, unsigned source){
  assert(target < size && source < size);
  if(find(target) == find(source))
    return;
  // ---------------------------------------------------------------------
  // Reverse the edges between the source
  // and its representative
  std::list<ExplainEquation> stack;
  unsigned aux_source = source;
  while(aux_source != proof_forest[aux_source]) {
    stack.push_back(ExplainEquation(aux_source, proof_forest[aux_source]));
    aux_source = proof_forest[aux_source];
  }
  while(!stack.empty()) {
    const auto element = stack.back();
    stack.pop_back();
    proof_forest[element.target] = element.source;
    if(stack.empty())
      proof_forest[element.source] = element.source;
  }
  // ---------------------------------------------------------------------

  proof_forest[source] = target;  

  UnionFind::merge(target, source);
  return;
}

std::ostream & UnionFindExplain::giveExplanation(std::ostream & os, unsigned x, unsigned y){
  os << "Explain " << x << ", " << y << std::endl;
  for(auto z : explain(x, y))
    os << z << std::endl;
  return os;
}

void UnionFindExplain::resize(unsigned sz){
  representative.resize(sz);
  rank.resize(sz);
  proof_forest.resize(sz);

  for(unsigned i = size; i < sz; i++){
    representative[i] = i;
    rank[i] = 1;
    proof_forest[i] = i;
  }

  size = sz;
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
      << " Forest: " << uf.proof_forest[i]
      << " Representative " << uf.find(i)
      << std::endl;
  }
  os << "Size " << uf.size << std::endl;
  os << "Num changes: " << num_changes;
  return os;
}
