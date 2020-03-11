#ifndef _CURRY_NODE_
#define _CURRY_NODE_ 

#include <iostream>
#include <string>
#include <map>
#include <vector>
#include <list>
#include <unordered_map>

template <class T>
inline void hash_combine(std::size_t & seed, const T & v, const std::hash<T> & hasher){
    seed ^= hasher(v) + 0x9e3779b9 + (seed<<6) + (seed>>2);
}

class CurryNode {
  
  unsigned id, z3_id;
  std::string func_name;
  CurryNode * left, * right;
  unsigned space = 1;
  
public:
  CurryNode(unsigned, std::string, CurryNode *, CurryNode *);
  const bool isConstant() const;
  const bool isReplaceable() const;
  void updateLeft(CurryNode *);
  void updateRight(CurryNode *);
  void updateZ3Id(unsigned);
  const unsigned getId() const;
  const unsigned getZ3Id() const;
  std::size_t hash();
  friend std::ostream & operator << (std::ostream &, const CurryNode &);
};

enum SideOfEquation { LHS, RHS } ;

struct PredPair {
  CurryNode * pred;
  SideOfEquation side_of_equation;
  PredPair(CurryNode * pred, SideOfEquation side_of_equation) :
    pred(pred), side_of_equation(side_of_equation){
  }
  friend std::ostream & operator << (std::ostream & os, const PredPair & pred_pair){
    os << *pred_pair.pred << " " << (pred_pair.side_of_equation == LHS ? "LHS" : "RHS");
    return os;
  }
};

typedef std::map<unsigned, CurryNode*>              CurryDeclarations;
typedef std::vector<CurryNode*>                     CurryNodes;
typedef std::map<CurryNode*, std::list<PredPair> >  CurryPreds;

#endif
