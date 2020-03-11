#ifndef _FAC_CURRY_NODES_
#define _FAC_CURRY_NODES_

#include <iostream>
#include <unordered_map>
#include <z3++.h>
#include "CurryNode.h"

class FactoryCurryNodes {
  friend class CongruenceClosureExplain;
  
  std::hash<unsigned>                         unsigned_hasher;
  std::hash<std::string>                      string_hasher;
  std::hash<CurryNode*>                       curry_hasher;
  std::unordered_map<std::size_t, CurryNode*> hash_table;
  
  const unsigned & num_terms;
  
  CurryNodes            curry_nodes;
  CurryNodes            extra_nodes;
  CurryDeclarations &   curry_decl;
  CurryPreds            curry_predecessors;
  std::list<CurryNode*> to_replace;
  
  unsigned              addExtraNodes(unsigned);
  void                  transferPreds(CurryNode *, CurryNode *);
  void                  curryficationHelper(z3::expr const &, std::vector<bool> &);
  void                  curryfication(z3::expr const &);
  void                  flattening();
  
 public:
  FactoryCurryNodes(const unsigned &, CurryDeclarations &);
  ~FactoryCurryNodes();
  CurryNode * newCurryNode(unsigned, std::string, CurryNode *, CurryNode *);
  CurryNode * getCurryNode(std::size_t) const;

  friend std::ostream & operator << (std::ostream &, const FactoryCurryNodes &);
};

#endif
