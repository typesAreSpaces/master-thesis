#ifndef UNIONFINDEXPLAIN_H
#define UNIONFINDEXPLAIN_H

#include <list>
#include <unordered_map>
#include "UnionFind.h"
 
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
  
  std::hash<unsigned> hasher;
  std::vector<unsigned> forest;
  std::vector<ExplainEquation> inserted_equations;
  std::unordered_map<std::size_t, unsigned> path;
  unsigned global_ticket;

  std::size_t hash_combine(unsigned, unsigned);
  unsigned depth(unsigned);
  unsigned commonAncestor(unsigned, unsigned);
  void explainHelper(unsigned, unsigned, ExplainEquations &);
  
public:
  UnionFindExplain();
  UnionFindExplain(unsigned);
  UnionFindExplain(const UnionFindExplain &);
  ~UnionFindExplain();
  void combine(unsigned, unsigned);
  void merge(unsigned, unsigned);
  ExplainEquations explain(unsigned, unsigned);
  void increaseSize(unsigned);
  bool operator ==(const UnionFindExplain &);
  friend std::ostream & operator << (std::ostream &, const UnionFindExplain &);
};

#endif
