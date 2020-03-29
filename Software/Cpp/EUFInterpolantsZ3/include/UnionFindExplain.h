#ifndef UNIONFINDEXPLAIN_H
#define UNIONFINDEXPLAIN_H

#include <list>
#include <unordered_map>
#include "UnionFind.h"
#include "CurryNode.h"

enum Direction { ORIENTED, REVERSED };

struct ExplainEquation {
  unsigned source, target;
  const PendingElement * label;
  
  ExplainEquation(unsigned source, unsigned target) :
    source(source), target(target), label(nullptr) {}

  ExplainEquation(unsigned source, unsigned target, const PendingElement * label) :
    source(source), target(target), label(label) {}
  
  friend std::ostream & operator << (std::ostream & os, const ExplainEquation & eq){
    os << eq.source << " := " << eq.target;
    if(eq.label == nullptr)
      os << "[no label]";
    else
      os << "[" << *eq.label << "]";
    return os;
  }
};

typedef std::list<const ExplainEquation *> ExplainEquations;
 
class UnionFindExplain :  public UnionFind {
  
  std::hash<unsigned>                       hasher;
  std::vector<unsigned>                     forest;
  // The following data structure is a persistant
  // vector with all the inserted equations
  std::vector<ExplainEquation>              inserted_equations;
  std::unordered_map<std::size_t, unsigned> path;
  unsigned                                  global_ticket;

  std::size_t hash_combine(unsigned, unsigned);
  unsigned depth(unsigned);
  unsigned commonAncestor(unsigned, unsigned);
  void     explainHelper(Direction, unsigned, unsigned, unsigned, ExplainEquations &);
  void     traverseExplain(unsigned, unsigned, ExplainEquations &);
  
public:
  UnionFindExplain();
  UnionFindExplain(unsigned);
  UnionFindExplain(const UnionFindExplain &);
  ~UnionFindExplain();
  void combine(unsigned, unsigned);
  void combine(unsigned, unsigned, const PendingElement *);
  void merge(unsigned, unsigned);
  void merge(unsigned, unsigned, const PendingElement *);
  ExplainEquations explain(unsigned, unsigned);
  std::ostream & giveExplanation(std::ostream &, unsigned, unsigned);
  void resize(unsigned);
  bool operator ==(const UnionFindExplain &);
  friend std::ostream & operator << (std::ostream &, UnionFindExplain &);
};

#endif
