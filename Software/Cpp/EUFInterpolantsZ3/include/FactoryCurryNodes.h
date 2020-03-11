#ifndef _FAC_CURRY_NODES_
#define _FAC_CURRY_NODES_

#include <iostream>
#include <unordered_map>
#include <z3++.h>
#include "CurryNode.h"

enum KindEquation { CONST_EQ, APPLY_EQ  };

struct PendingElement {
};

struct EquationCurryNodes {
  CurryNode * lhs, * rhs;
  KindEquation kind_equation;
  EquationCurryNodes() : lhs(nullptr), rhs(nullptr), kind_equation(CONST_EQ) {}
  EquationCurryNodes(CurryNode * lhs, CurryNode * rhs) :
  lhs(lhs), rhs(rhs), kind_equation(lhs->isConstant() ? CONST_EQ : APPLY_EQ) {}
  EquationCurryNodes(CurryNode * lhs, CurryNode * rhs, KindEquation kind_equation) :
    lhs(lhs), rhs(rhs), kind_equation(kind_equation) {}
  friend std::ostream & operator << (std::ostream & os, const EquationCurryNodes & ecns){
    os << *ecns.lhs << " = " << *ecns.rhs;
    return os;
  }
};



struct EquationZ3Ids {
  unsigned lhs_id, rhs_id;
  EquationZ3Ids(unsigned lhs_id, unsigned rhs_id) :
    lhs_id(lhs_id), rhs_id(rhs_id) {}
  friend std::ostream & operator << (std::ostream & os, const EquationZ3Ids & ez3ids){
    os << ez3ids.lhs_id << " = " << ez3ids.rhs_id;
    return os;
  }
};

typedef std::list<EquationCurryNodes> PendingExplain;
typedef std::list<EquationZ3Ids>      IdsToMerge;

class FactoryCurryNodes {
  friend class CongruenceClosureExplain;
  
  std::hash<unsigned>                         unsigned_hasher;
  std::hash<std::string>                      string_hasher;
  std::hash<CurryNode*>                       curry_hasher;
  std::unordered_map<std::size_t, CurryNode*> hash_table;
  CurryNodes                                  id_table;
  
  const unsigned & num_terms;
  
  CurryNodes                curry_nodes;
  CurryNodes                extra_nodes;
  const CurryDeclarations & curry_decl;
  CurryPreds                curry_predecessors;
  std::list<CurryNode*>     to_replace;
  
  unsigned   addExtraNodes(unsigned);
  void       updatePreds(CurryNode *, CurryNode *);
  void       curryficationHelper(z3::expr const &, std::vector<bool> &, IdsToMerge &);
  IdsToMerge curryfication(z3::expr const &);
  void       flattening(const unsigned &, PendingExplain &);
  
 public:
  FactoryCurryNodes(const unsigned &, const CurryDeclarations &);
  ~FactoryCurryNodes();
  
  CurryNode * newCurryNode(unsigned, std::string, CurryNode *, CurryNode *);
  CurryNode * getCurryNode(std::size_t) const;

  const unsigned size() const;

  friend std::ostream & operator << (std::ostream &, const FactoryCurryNodes &);
};

#endif
