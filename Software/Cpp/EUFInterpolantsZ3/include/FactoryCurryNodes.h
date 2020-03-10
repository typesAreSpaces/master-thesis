#ifndef _FAC_CURRY_NODES_
#define _FAC_CURRY_NODES_

#include <iostream>
#include <unordered_map>
#include "CurryNode.h"

class FactoryCurryNodes {
  
  std::hash<unsigned>                         unsigned_hasher;
  std::hash<std::string>                      string_hasher;
  std::hash<CurryNode*>                       curry_hasher;
  std::unordered_map<std::size_t, CurryNode*> hash_table;
  
 public:
  FactoryCurryNodes();
  ~FactoryCurryNodes();
  CurryNode * newCurryNode(unsigned, std::string, CurryNode *, CurryNode *);
  CurryNode * getCurryNode(std::size_t);
};

#endif
