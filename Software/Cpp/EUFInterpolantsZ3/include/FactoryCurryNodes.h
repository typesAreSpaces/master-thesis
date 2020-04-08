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
  VectorCurryNode                             id_table;
  
  const unsigned & num_terms;
  
  VectorCurryNode           curry_nodes;
  VectorCurryNode           extra_nodes;
  const CurryDeclarations & curry_decl;
  CurryPreds                curry_predecessors;
  std::list<CurryNode *>    to_replace;
  
  unsigned   addExtraNodes(unsigned);
  void       updatePreds(CurryNode *, CurryNode *);
  void       updateZ3IdNotDefined(const z3::expr_vector &);
  void       curryficationHelper(z3::expr const &, std::vector<bool> &, IdsToMerge &);
  IdsToMerge curryfication(z3::expr const &);
  void       flattening(const unsigned &, PendingElements &, PendingPointers &, const z3::expr_vector &);
  
 public:
  FactoryCurryNodes(const unsigned &, const CurryDeclarations &);
  ~FactoryCurryNodes();
  
  CurryNode * newCurryNode(unsigned, std::string, CurryNode *, CurryNode *);
  CurryNode * getCurryNode(std::size_t) const;
  CurryNode * constantZ3Index(unsigned);
  CurryNode * constantCurryNode(unsigned);

  const unsigned size() const;
  const unsigned uniqueSize() const;

  friend std::ostream & operator << (std::ostream &, const FactoryCurryNodes &);
};

#endif
