#ifndef _CIRCULAR_LIST_
#define _CIRCULAR_LIST_

#include <iostream>
#include "Node.h"

template <typename T>
class CircularList{
 private:
  int length;
  node<T> * list;
  void addEmpty(T x);
  void addNonEmpty(T x);
 public:
  CircularList();
  ~CircularList();
  int size();
	void add(T x);
  void merge(CircularList *);
	node<T> * getList();
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
	std::ostream & print(std::ostream &);
};

#endif
