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
    sig_table[hash_combine(a1, a2)] = ecn;
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

typedef std::vector<std::list<EquationCurryNodes> > UseList;
typedef std::vector<std::list<unsigned> >           ClassListExplain;

class CongruenceClosureExplain : public CongruenceClosure {
  
  friend class Hornsat;

  unsigned num_terms;
  
  PendingExplain   pending_explain;
  LookupTable      lookup_table;
  UseList          use_list;
  ClassListExplain class_list_explain;

  void merge(const PendingElement &);
  void propagate();
  
 public:
  CongruenceClosureExplain(const unsigned &, const z3::expr_vector &,
			   PredList &, UnionFindExplain &,
			   const CurryDeclarations &, FactoryCurryNodes &);
  void buildCongruenceClosure(std::list<unsigned> &);
  
  ~CongruenceClosureExplain();
  friend std::ostream & operator << (std::ostream &, const CongruenceClosureExplain &);
};


#endif
