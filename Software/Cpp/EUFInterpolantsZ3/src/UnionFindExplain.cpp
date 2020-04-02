#include "UnionFindExplain.h"
#define DEBUG_DESTRUCTOR_UFE false
#define DEBUG_EXPLAIN_OP false

UnionFindExplain::UnionFindExplain() :
  UnionFind(0) { 
  };

UnionFindExplain::UnionFindExplain(unsigned size) :
  UnionFind(size), proof_forest(size, 0), labels(size, nullptr) {
    for(unsigned i = 0; i < size; i++)
      proof_forest[i] = i;
  }

UnionFindExplain::UnionFindExplain(const UnionFindExplain & other) :
  UnionFind(other), proof_forest(other.proof_forest) , labels(other.labels) {
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

unsigned UnionFindExplain::commonAncestor(unsigned x, unsigned y) {
  if(find(x) == find(y))
    return getRootProofForest(x);
  throw "The nodes are not in the same equivalence class";
}

void UnionFindExplain::explainAlongPath(unsigned a, unsigned c) {
  a = getRootProofForest(a);
  while(a != c) {
    unsigned b = proof_forest[a];
    // TODO: Keep working here
  }
}

ExplainEquations UnionFindExplain::explain(unsigned x, unsigned y){
  ExplainEquations explanations;
  std::list<ExplainEquation> pending_proofs;
  pending_proofs.push_back(ExplainEquation(x, y));

  while(!pending_proofs.empty()){
    const auto current_equation = pending_proofs.back();
    pending_proofs.pop_back();
    unsigned c = commonAncestor(current_equation.source, current_equation.target);
    explainAlongPath(current_equation.source, c);
    explainAlongPath(current_equation.target, c);
  }

  return explanations;
}

// The first argument becomes the new
// representative, always.
void UnionFindExplain::combine(unsigned target, unsigned source){
  assert(target < size && source < size);
  if(find(target) == find(source))
    return;

  // Dealing with proof_forest
  unsigned explain_source = proof_forest[find(source)], explain_target = proof_forest[find(target)];
  inserted_equations.emplace_back(source, target);
  proof_forest[find(source)] = explain_target;
  // path[hash_combine(explain_source, explain_target)] = global_ticket++;

  UnionFind::combine(target, source); 
  return;
}

// The first argument becomes the new
// representative, always.
void UnionFindExplain::combine(unsigned target, unsigned source, const PendingElement * pe){
  assert(target < size && source < size);
  if(find(target) == find(source))
    return;

  // Dealing with proof_forest
  unsigned explain_source = proof_forest[find(source)], explain_target = proof_forest[find(target)];
  inserted_equations.emplace_back(source, target, pe);
  proof_forest[find(source)] = explain_target;
  // path[hash_combine(explain_source, explain_target)] = global_ticket++;

  UnionFind::combine(target, source); 
  return;
}

// The first argument becomes the new
// representative in proof_forest, always.
void UnionFindExplain::merge(unsigned target, unsigned source){
  assert(target < size && source < size);
  if(find(target) == find(source))
    return;

  // Dealing with proof_forest 
  unsigned explain_source = proof_forest[find(source)], explain_target = proof_forest[find(target)];
  inserted_equations.emplace_back(source, target);
  proof_forest[find(source)] = explain_target;  
  // path[hash_combine(explain_source, explain_target)] = global_ticket++;

  UnionFind::merge(target, source);
  return;
}

// The first argument becomes the new
// representative in proof_forest, always.
void UnionFindExplain::merge(unsigned target, unsigned source, const PendingElement * pe){
  assert(target < size && source < size);
  if(find(target) == find(source))
    return;

  // Dealing with proof_forest 
  unsigned explain_source = proof_forest[find(source)], explain_target = proof_forest[find(target)];
  inserted_equations.emplace_back(source, target, pe);
  proof_forest[find(source)] = explain_target;  
  // path[hash_combine(explain_source, explain_target)] = global_ticket++;

  UnionFind::merge(target, source);
  return;
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
  proof_forest.resize(sz);
  labels.resize(sz);

  for(unsigned i = size; i < sz; i++){
    representative[i] = i;
    rank[i] = 1;
    proof_forest[i] = i;
    labels[i] = nullptr;
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
