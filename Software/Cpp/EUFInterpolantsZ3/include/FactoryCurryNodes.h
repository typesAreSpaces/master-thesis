#ifndef _FAC_CURRY_NODES_
#define _FAC_CURRY_NODES_

#include <iostream>
#include <unordered_map>
#include <z3++.h>
#include "Z3Subterms.h"
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
  void       updateZ3IdNotDefinedAndCommon(const Z3Subterms &);
  void       curryficationHelper(z3::expr const &, std::vector<bool> &, IdsToMerge &);
  IdsToMerge curryfication(z3::expr const &);
  void       flattening(PendingElements &, PendingPointers &, const Z3Subterms &);
  
 public:
  FactoryCurryNodes(const unsigned &, const CurryDeclarations &);
  ~FactoryCurryNodes();
  
  CurryNode * newCurryNode(unsigned, std::string, CurryNode *, CurryNode *);
  CurryNode * getCurryNode(std::size_t) const;
  CurryNode * constantZ3Index(unsigned);
  CurryNode * constantCurryNode(unsigned);
  CurryNode * getCurryNodeById(unsigned) const;

  const unsigned size() const;
  const unsigned uniqueSize() const;

  friend std::ostream & operator << (std::ostream &, const FactoryCurryNodes &);
};

#endif
