#ifndef _CIRCULAR_LIST_
#define _CIRCULAR_LIST_

#include <iostream>
#include "Node.h"

template <typename T>
class CircularList;

template <typename T>
std::ostream & operator << (std::ostream &, CircularList<T> &);

template <typename T>
class CircularList{
 private:
  unsigned int length;
  node<T> * elements;
  void addEmpty(T);
  void addNonEmpty(T);
	
 public:
  CircularList();
  ~CircularList();
  unsigned int size();
  void add(T);
  void merge(CircularList *);
  node<T> * getElements();
  node<T> * begin();
  node<T> * end();
  bool empty();
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
  template <typename U>
    friend std::ostream & operator << (std::ostream &, CircularList<U> &);
};

#include "CircularList.tpp"

#endif
