#ifndef NODE_H
#define NODE_H

#include <iostream> 
#include <cstddef>

template <typename T>
struct node {
  T data;
  struct node * next;
};

#endif
