#ifndef NODE_H
#define NODE_H

#include <iostream> 
#include <cstddef>

typedef struct node {
  int data;
  struct node * next;
} node;

class LinkedList{
 private:
  int count;
  node *head, *tail;
 public:
  LinkedList();
  void add(int x);
  int size();
  node * getList();
  std::ostream & print(std::ostream &);
};

class CircularList{
 private:
  int count;
  node * tail;
 public:
  CircularList();
  void add(int x);
  void addEmpty(int x);
  void addNonEmpty(int x);
  int size();
  std::ostream & print(std::ostream &);
};

#endif
