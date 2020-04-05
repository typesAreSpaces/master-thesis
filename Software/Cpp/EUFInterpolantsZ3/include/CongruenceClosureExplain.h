#ifndef _CONG_CLOSURE_E__
#define _CONG_CLOSURE_E__

#include <map>
#include <set>
#include "CongruenceClosure.h"
#include "FactoryCurryNodes.h"

class LookupTable {
  std::unordered_map<std::size_t, const EquationCurryNodes*> sig_table;
  std::hash<unsigned> unsigned_hasher;

  public:
  LookupTable() {}
  ~LookupTable(){
#if DEBUG_DESTRUCTORS_CC
    std::cout << "Done ~LookupTable" << std::endl;
#endif
  }
  std::size_t hash_combine(unsigned a1, unsigned a2){
    std::size_t seed = unsigned_hasher(a1);
    seed ^= unsigned_hasher(a2) + 0x9e3779b9 + (seed << 6) + (seed >> 2);
    return seed;
  }
  void enter(unsigned a1, unsigned a2, const EquationCurryNodes * ecn){
    auto index = hash_combine(a1, a2);
    sig_table[index] = ecn;
    return;
  }
  void erase(unsigned a1, unsigned a2){
    sig_table.erase(hash_combine(a1, a2));
  }
  const EquationCurryNodes * query(unsigned a1, unsigned a2){
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

  unsigned            num_terms;
  FactoryCurryNodes & factory_curry_nodes;
  UnionFindExplain &  ufe;

  PendingElements         pending_elements;
  PendingElementsPointers equations_to_merge;
  PendingElementsPointers pending_to_propagate;

  LookupTable lookup_table;
  UseList     use_list;

  void     pushPending(PendingElementsPointers &, const PendingElement &);
  unsigned highestNode(unsigned, UnionFind &);
  unsigned nearestCommonAncestor(unsigned, unsigned, UnionFind &);
  void     merge();
  void     propagate();
  void     propagateAux(const CurryNode &, const CurryNode &, unsigned, unsigned, const PendingElement &);
  // Both of the unsigned inputs to explain encode the identifier in
  // some equivalence class structure
  PendingElementsPointers explain(unsigned, unsigned);
  void                    explainAlongPath(unsigned, unsigned, UnionFind &, ExplainEquations &, PendingElementsPointers &);

  public:
  CongruenceClosureExplain(const unsigned &, const z3::expr_vector &,
      PredList &, UnionFindExplain &, FactoryCurryNodes &);
  void buildCongruenceClosure(std::list<unsigned> &);
  void merge(const EquationCurryNodes &);
  PendingElementsPointers explain(const z3::expr &, const z3::expr &);
  std::ostream & giveExplanation(std::ostream &, const z3::expr &, const z3::expr &);

  ~CongruenceClosureExplain();
  friend std::ostream & operator << (std::ostream &, const CongruenceClosureExplain &);
};


#endif
