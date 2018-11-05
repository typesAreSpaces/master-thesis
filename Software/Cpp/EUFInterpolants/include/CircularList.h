#ifndef _CIRCULAR_LIST_
#define _CIRCULAR_LIST_

#include <iostream>
#include "Node.h"

template <typename T>
class CircularList{
 private:
  int length;
  node<T> * tail;
  void addEmpty(T x);
  void addNonEmpty(T x);
	void setLength(int);
 public:
  CircularList();
  ~CircularList();
  void add(T x);
  int size();
  node<T> * getList();
  void mergeCircularList(CircularList *);
  std::ostream & print(std::ostream &);
	node<T> * begin();
  node<T> * end();
  class iterator{
  private:
    node<T> * _it;
  public:
    iterator(node<T>*);
    ~iterator();
    iterator& operator++();
    bool operator==(node<T> *) const;
    bool operator!=(node<T> *) const;
    node<T>& operator*();
  };
};

#endif
