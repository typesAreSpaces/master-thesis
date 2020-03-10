#ifndef _FAC_CURRY_NODES_
#define _FAC_CURRY_NODES_

#include <iostream>
#include <unordered_map>
#include "CurryNode.h"

class FactoryCurryNodes {
  friend class CongruenceClosureExplain;
  
  std::hash<unsigned>                         unsigned_hasher;
  std::hash<std::string>                      string_hasher;
  std::hash<CurryNode*>                       curry_hasher;
  std::unordered_map<std::size_t, CurryNode*> hash_table;

protected:
  CurryPreds            curry_predecessors;
  std::list<CurryNode*> to_replace;
  void                  transferPreds(CurryNode *, CurryNode *);
  
 public:
  FactoryCurryNodes();
  ~FactoryCurryNodes();
  CurryNode * newCurryNode(unsigned, std::string, CurryNode *, CurryNode *);
  CurryNode * getCurryNode(std::size_t) const;

  friend std::ostream & operator << (std::ostream &, const FactoryCurryNodes &);
};

#endif
