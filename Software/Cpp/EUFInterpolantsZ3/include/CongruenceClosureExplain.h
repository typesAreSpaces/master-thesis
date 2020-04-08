#ifndef _CONG_CLOSURE_E__
#define _CONG_CLOSURE_E__

#include <map>
#include <set>
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
  std::size_t hash_combine(EqClass a1, EqClass a2){
    std::size_t seed = EqClass_hasher(a1);
    seed ^= EqClass_hasher(a2) + 0x9e3779b9 + (seed << 6) + (seed >> 2);
    return seed;
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

class CongruenceClosureExplain;
template<typename T>
std::ostream & giveExplanation(std::ostream &, const CongruenceClosureExplain &, const T &, const T &);

class CongruenceClosureExplain : public CongruenceClosure {

  friend class Hornsat;

  unsigned                num_terms;
  const z3::expr_vector & subterms;
  FactoryCurryNodes &     factory_curry_nodes;
  UnionFindExplain &      ufe;

  PendingElements         pending_elements;
  PendingElementsPointers equations_to_merge;
  PendingElementsPointers pending_to_propagate;

  LookupTable lookup_table;
  UseList     use_list;

  void    pushPending(PendingElementsPointers &, const PendingElement &);
  EqClass highestNode(EqClass, UnionFind &);
  EqClass nearestCommonAncestor(EqClass, EqClass, UnionFind &);
  void    merge();
  void    propagate();
  void    propagateAux(const CurryNode &, const CurryNode &, EqClass, EqClass, const PendingElement &);
  void    explainAlongPath(EqClass, EqClass, UnionFind &, ExplainEquations &, PendingElementsPointers &);

  public:
  CongruenceClosureExplain(const unsigned &, const z3::expr_vector &,
      PredList &, UnionFindExplain &, FactoryCurryNodes &);
  void buildCongruenceClosure(std::list<EqClass> &);
  void merge(const EquationCurryNodes &);
  PendingElementsPointers explain(const z3::expr &, const z3::expr &);
  PendingElementsPointers explain(EqClass, EqClass);
  std::ostream & giveExplanation(std::ostream &, const z3::expr &, const z3::expr &);
  std::ostream & giveExplanation(std::ostream &, EqClass, EqClass);
  Z3ElementsPointers z3Explain(const z3::expr &, const z3::expr &);
  std::ostream & giveZ3Explanation(std::ostream &, const z3::expr &, const z3::expr &, const z3::expr_vector &);

  ~CongruenceClosureExplain();
  friend std::ostream & operator << (std::ostream &, const CongruenceClosureExplain &);
};

#endif
