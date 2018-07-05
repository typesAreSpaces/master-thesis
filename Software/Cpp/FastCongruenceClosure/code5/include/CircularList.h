#ifndef _CIRCULAR_LIST_
#define _CIRCULAR_LIST_

#include <iostream>
#include "node.h"

template <typename T>
class CircularList{
 private:
  int length;
  node<T> * tail;
  void addEmpty(T x);
  void addNonEmpty(T x);
 public:
  CircularList();
  ~CircularList();
  void add(T x);
  int size();
  node<T> * getList();
  void setLength(int);
  void mergeCircularList(CircularList *);
  std::ostream & print(std::ostream &);
};

#endif
