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

  static std::hash<unsigned>                         unsigned_hasher;
  static std::hash<std::string>                      string_hasher;
  static std::hash<CurryNode*>                       curry_hasher;
  
public:
  CurryNode(unsigned, std::string, CurryNode *, CurryNode *);
  const bool isConstant() const;
  const bool isReplaceable() const;
  std::size_t hash();
  friend std::ostream & operator << (std::ostream &, const CurryNode &);

  static void * operator new (std::size_t, unsigned, std::string, CurryNode *, CurryNode *);
  static CurryNode * newCurryNode(unsigned, std::string, CurryNode *, CurryNode *);
  static void removePointers();

  static std::unordered_map<std::size_t, CurryNode*> hash_table;
};

#endif
