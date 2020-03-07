#ifndef _CONG_CLOSURE_E__
#define _CONG_CLOSURE_E__

#include <map>
#include "CongruenceClosure.h"
#include "CurryNode.h"

struct EquationCurryNodes {
  CurryNode * lhs, * rhs;
  EquationCurryNodes(CurryNode * lhs, CurryNode * rhs) :
    lhs(lhs), rhs(rhs) {}
  friend std::ostream & operator << (std::ostream & os, const EquationCurryNodes & ecns){
    os << *ecns.lhs << " = " << *ecns.rhs;
    return os;
  }
};

typedef std::vector<std::list<unsigned> > CCList;
typedef std::map<unsigned, CurryNode*>    CurryDeclarations;
typedef std::vector<CurryNode*>           CurryNodes;
typedef std::list<EquationCurryNodes>     PendingExplain;

class CongruenceClosureExplain : public CongruenceClosure {
  friend class Hornsat;

  unsigned                  num_terms;
  CurryNodes                curry_nodes;
  CurryNodes                extra_nodes;
  CurryDeclarations &       curry_decl;
  PendingExplain            pending_explain;

  void curryfication(z3::expr const &, std::vector<bool> &);
  void merge(CurryNode *, CurryNode *);
  
 public:
  CongruenceClosureExplain(const unsigned &, const z3::expr_vector &, CCList &, UnionFind &, CurryDeclarations &);
  void buildCongruenceClosure(std::list<unsigned> &);
  
  ~CongruenceClosureExplain();
  friend std::ostream & operator << (std::ostream &, const CongruenceClosureExplain &);
};


#endif
