#include <iostream>
#include "LinkedList.h"

template <typename T>
LinkedList<T>::LinkedList() : head(nullptr), tail(nullptr), length(0) {}

template <typename T>
LinkedList<T>::~LinkedList(){
  node<T> * ptr;
  ptr = head;
  while(ptr){
    head = head->next;    
    delete ptr;
    ptr = head;
  }
}

template <typename T>
void LinkedList<T>::add(T x){
  node<T> * temp = new node<T>;
  temp->data = x;
  temp->next = nullptr;
  if(head == nullptr){
    head = temp;
    tail = temp;
  }
  else{
    tail->next = temp;
    tail = temp;
  }
  ++length;
}

template <typename T>
int LinkedList<T>::size(){
  return length;
}

template <typename T>
node<T> * LinkedList<T>::getList(){
  return head;
}

template <typename T>
std::ostream & operator << (std::ostream & os, LinkedList<T> & l){
  node<T> * temp;
  for(temp = l.head; temp != nullptr; temp = temp->next)
    os << temp->data << " ";
  os << std::endl;
  return os;
}
