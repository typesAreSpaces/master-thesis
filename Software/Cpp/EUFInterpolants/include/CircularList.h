#ifndef _CIRCULAR_LIST_
#define _CIRCULAR_LIST_

#include <iostream>
#include "Node.h"

template <typename T>
class CircularList;

template <typename T>
std::ostream & operator << (std::ostream &, CircularList<T> &);

template <typename T>
class CircularList {
  
  unsigned int length;
  Node<T> * elements;
  void addEmpty(const T &);
  void addNonEmpty(const T &);
  
public:
  CircularList();
  ~CircularList();
  unsigned int size();
  void add(const T &);
  void merge(CircularList &);
  bool empty();
  const Node<T> & getElements();
  
  Node<T> * begin();
  Node<T> * end();
  class iterator{
  private:
    Node<T> * _it;
  public:
    iterator(Node<T>*);
    ~iterator();
    iterator& operator++();
    bool operator==(Node<T> *) const;
    bool operator!=(Node<T> *) const;
    Node<T>& operator*();
  };
  template <typename U>
  friend std::ostream & operator << (std::ostream &, CircularList<U> &);
  template <typename U>
  friend std::ostream & operator << (std::ostream &, CircularList<U*> &);
};

#include "CircularList.tpp"

#endif
