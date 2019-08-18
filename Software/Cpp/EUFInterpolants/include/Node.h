#ifndef NODE_H
#define NODE_H

#include <cstddef>

template <typename T>
struct node {
  T data;
  struct node * next;
};

#endif
