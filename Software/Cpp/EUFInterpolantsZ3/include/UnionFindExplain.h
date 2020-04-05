#ifndef UNIONFINDEXPLAIN_H
#define UNIONFINDEXPLAIN_H

#include <list>
#include <unordered_map>
#include <algorithm>
#include "UnionFind.h"
#include "CurryNode.h"

struct ExplainEquation {
  unsigned source, target;
  
  ExplainEquation(unsigned source, unsigned target) :
    source(source), target(target) {}

  friend std::ostream & operator << (std::ostream & os, const ExplainEquation & eq){
    os << eq.source << " := " << eq.target;
    return os;
  }
};

typedef std::list<ExplainEquation> ExplainEquations;
 
class UnionFindExplain :  public UnionFind {
  
  std::vector<unsigned>               proof_forest;

  std::hash<unsigned>   hasher;
  std::size_t           hash_combine(unsigned, unsigned);

  void     unionReverseEdges(unsigned, unsigned);
  unsigned depth(unsigned);
  unsigned commonAncestorHelper(unsigned, unsigned, unsigned);
  unsigned commonAncestor(unsigned, unsigned);
  void     explainAlongPath(unsigned, unsigned, ExplainEquations &);
  
public:
  UnionFindExplain();
  UnionFindExplain(unsigned);
  UnionFindExplain(const UnionFindExplain &);
  ~UnionFindExplain();

  unsigned         parentProofForest(unsigned);
  ExplainEquations explain(unsigned, unsigned);
  void             combine(unsigned, unsigned);
  void             merge(unsigned, unsigned);

  std::ostream & giveExplanation(std::ostream &, unsigned, unsigned);
  void           resize(unsigned);

  friend std::ostream & operator << (std::ostream &, UnionFindExplain &);
};

#endif
