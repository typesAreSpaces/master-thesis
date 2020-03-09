#ifndef _CONG_CLOSURE_E__
#define _CONG_CLOSURE_E__

#include <map>
#include <set>
#include "CongruenceClosure.h"
#include "CurryNode.h"

enum KindEquation { CONST_EQ, APPLY_EQ  };

struct EquationCurryNodes {
  CurryNode * lhs, * rhs;
  KindEquation kind_equation;
  EquationCurryNodes() : lhs(nullptr), rhs(nullptr), kind_equation(CONST_EQ) {}
  EquationCurryNodes(CurryNode * lhs, CurryNode * rhs, KindEquation kind_equation) :
    lhs(lhs), rhs(rhs), kind_equation(kind_equation) {}
  friend std::ostream & operator << (std::ostream & os, const EquationCurryNodes & ecns){
    os << *ecns.lhs << " = " << *ecns.rhs;
    return os;
  }
};

class LookupTable {
  std::unordered_map<std::size_t, EquationCurryNodes> sig_table;
  UnionFind & uf;
  std::hash<unsigned> hash_unsigned;
  
public:
  LookupTable(UnionFind & uf) : uf(uf){}
  ~LookupTable(){
#if DEBUG_DESTRUCTORS_CC
    std::cout << "Done ~LookupTable" << std::endl;
#endif
  }
  std::size_t hash_combine(unsigned a1, unsigned a2){
    std::size_t seed = hash_unsigned(a1);
    seed ^= hash_unsigned(a2) + 0x9e3779b9 + (seed << 6) + (seed >> 2);
    return seed;
  }
  void enter(unsigned a1, unsigned a2, EquationCurryNodes ecn){
    sig_table[hash_combine(a1, a2)] = ecn;
  }
  void erase(unsigned a1, unsigned a2){
    sig_table.erase(hash_combine(a1, a2));
  }
  EquationCurryNodes query(unsigned a1, unsigned a2){
    auto r = sig_table.find(hash_combine(a1, a2));
    if(r == sig_table.end())
      throw "Element not in the table";
    return r->second;
  }
  friend std::ostream & operator << (std::ostream & os, const LookupTable & st){
    return os;
  }
};

typedef std::vector<std::list<unsigned> >            CCList;
typedef std::map<CurryNode*, std::list<CurryNode*> > PredExplain;
typedef std::map<unsigned, CurryNode*>               CurryDeclarations;
typedef std::vector<CurryNode*>                      CurryNodes;
typedef std::list<EquationCurryNodes>                PendingExplain;
typedef std::vector<std::list<EquationCurryNodes> >  UseList;

class CongruenceClosureExplain : public CongruenceClosure {
  friend class Hornsat;

  unsigned num_terms;
  
  CurryNodes            curry_nodes;
  CurryNodes            extra_nodes;
  CurryDeclarations &   curry_decl;
  PredExplain           predecessors;
  std::set<std::size_t> to_replace;
  
  PendingExplain pending_explain;
  LookupTable lookup_table;
  UseList     use_list;
  CCList      class_list_explain;

  void curryfication(z3::expr const &, std::vector<bool> &);
  void merge(CurryNode *, CurryNode *);
  void propagate();
  
 public:
  CongruenceClosureExplain(const unsigned &, const z3::expr_vector &, CCList &, UnionFind &, CurryDeclarations &);
  void buildCongruenceClosure(std::list<unsigned> &);
  
  ~CongruenceClosureExplain();
  friend std::ostream & operator << (std::ostream &, const CongruenceClosureExplain &);
};


#endif
