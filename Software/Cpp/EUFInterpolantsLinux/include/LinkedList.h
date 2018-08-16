#ifndef _LINKED_LIST_
#define _LINKED_LIST_

#include <iostream>
#include "Node.h"

template <typename T>
class LinkedList{
 private:
  int length;
  node<T> *head, *tail;
 public:
  LinkedList();
  ~LinkedList();
  void add(T x);
  int size();
  node<T> * getList();
  std::ostream & print(std::ostream &);
};

#endif
