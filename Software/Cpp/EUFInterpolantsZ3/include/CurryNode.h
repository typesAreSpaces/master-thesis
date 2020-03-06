#ifndef _CURRY_NODE_
#define _CURRY_NODE_ 

#include <iostream>
#include <string>

class CurryNode {
  unsigned id;
  std::string func_name;
  CurryNode * left, * right;
public:
  CurryNode(unsigned);
  CurryNode(unsigned, std::string, CurryNode *, CurryNode *);
  CurryNode(const CurryNode &);
  void update(std::string, CurryNode *, CurryNode *);
  void changeId(unsigned);
  const unsigned getId() const;
  friend std::ostream & operator << (std::ostream &, const CurryNode &);
};

#endif
