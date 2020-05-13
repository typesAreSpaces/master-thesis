#ifndef _CONG_CLOSURE_E__
#define _CONG_CLOSURE_E__

#include <map>
#include <set>
#include "Z3Subterms.h"
#include "CongruenceClosure.h"
#include "FactoryCurryNodes.h"

class LookupTable {
  std::unordered_map<std::size_t, const EquationCurryNodes*> sig_table;
  std::hash<EqClass> EqClass_hasher;

  public:
  LookupTable() {}
  ~LookupTable(){
#if DEBUG_DESTRUCTORS_CC
    std::cout << "Done ~LookupTable" << std::endl;
#endif
  }
  //std::size_t hash_combine(EqClass a1, EqClass a2){
    //std::size_t seed = EqClass_hasher(a1);
    //seed ^= EqClass_hasher(a2) + 0x9e3779b9 + (seed << 6) + (seed >> 2);
    //return seed;
  //}
  std::size_t hash_combine(EqClass a1, EqClass a2){
    return std::hash<unsigned long long>()(((unsigned long long) a1) ^ (((unsigned long long) a2) << 32));
  }
  void enter(EqClass a1, EqClass a2, const EquationCurryNodes * ecn){
    auto index = hash_combine(a1, a2);
    sig_table[index] = ecn;
    return;
  }
  void erase(EqClass a1, EqClass a2){
    sig_table.erase(hash_combine(a1, a2));
  }
  const EquationCurryNodes * query(EqClass a1, EqClass a2){
    auto r = sig_table.find(hash_combine(a1, a2));
    if(r == sig_table.end())
      return nullptr;
    return r->second;
  }
  friend std::ostream & operator << (std::ostream & os, const LookupTable & lt){
    for(auto x : lt.sig_table)
      os << *(x.second) << std::endl;
    os << "Size of lookup table: " << lt.sig_table.size();
    return os;
  }
};

typedef std::vector<std::list<const EquationCurryNodes *> > UseList;

class CongruenceClosureExplain : public CongruenceClosure {

  friend class Hornsat;

  FactoryCurryNodes & factory_curry_nodes;

  PendingElements pending_elements;
  PendingPointers equations_to_merge;
  PendingPointers pending_to_propagate;

  LookupTable lookup_table;
  UseList     use_list;

  void    pushPending(PendingPointers &, const PendingElement &);
  EqClass highestNode(EqClass, UnionFind &);
  EqClass nearestCommonAncestor(EqClass, EqClass, UnionFind &);
  void    merge();
  void    propagate();
  void    propagateAux(const CurryNode &, const CurryNode &, EqClass, EqClass, const PendingElement &);
  void    explainAlongPath(EqClass, EqClass, UnionFind &, ExplainEquations &, PendingPointers &);

  public:
  CongruenceClosureExplain(const Z3Subterms &, UnionFindExplain &, FactoryCurryNodes &, IdsToMerge const &);
  ~CongruenceClosureExplain();

  void buildCongruenceClosure(std::list<EqClass> &);

  void merge(EquationCurryNodes const &);
  void merge(z3::expr const &, z3::expr const &);

  PendingPointers explain(const z3::expr &, const z3::expr &);
  PendingPointers explain(EqClass, EqClass);

  std::ostream & giveExplanation(std::ostream &, const z3::expr &, const z3::expr &);
  std::ostream & giveExplanation(std::ostream &, EqClass, EqClass);

  Z3EquationPointers z3Explain(const z3::expr &, const z3::expr &);
  std::ostream & giveZ3Explanation(std::ostream &, const z3::expr &, const z3::expr &);
  
  z3::expr z3_repr(unsigned);
  z3::expr z3_repr(z3::expr const &);

  friend std::ostream & operator << (std::ostream &, const CongruenceClosureExplain &);
};

#endif
