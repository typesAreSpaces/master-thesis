#ifndef _CURRY_NODE_
#define _CURRY_NODE_ 

#include <iostream>
#include <string>
#include <unordered_map>

template <class T>
inline void hash_combine(std::size_t & seed, const T & v, const std::hash<T> & hasher){
    seed ^= hasher(v) + 0x9e3779b9 + (seed<<6) + (seed>>2);
}

class CurryNode {
  
  unsigned id;
  std::string func_name;
  CurryNode * left, * right;
  unsigned space = 1;
  
public:
  CurryNode(unsigned, std::string, CurryNode *, CurryNode *);
  const bool isConstant() const;
  const bool isReplaceable() const;
  std::size_t hash();
  friend std::ostream & operator << (std::ostream &, const CurryNode &);
};

#endif
