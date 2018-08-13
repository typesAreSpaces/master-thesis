#include <iostream>
#include "CircularList.h"

template <typename T>
CircularList<T>::CircularList() : length(0), tail(nullptr) {}

template <typename T>
CircularList<T>::~CircularList(){
  node<T> * ptr;
  if(length != 0){
    ptr = tail->next;
    while(ptr != ptr->next){
      tail->next = ptr->next;
      delete ptr;
      ptr = tail->next;
    }
   delete ptr; 
  }
}

template <typename T>
void CircularList<T>::add(T x){
  if(length == 0)
    addEmpty(x);
  else
    addNonEmpty(x);
  ++length;
}

template <typename T>
void CircularList<T>::addEmpty(T x){
  tail = nullptr;
  node<T> * temp = new node<T>;
  temp->data = x;
  temp->next = nullptr;
  temp->next = temp;
  tail = temp;
}

template <typename T>
void CircularList<T>::addNonEmpty(T x){
  node<T> * temp = new node<T>;
  temp->data = x;
  temp->next = tail->next;
  tail->next = temp;
  tail = temp;
}

template <typename T>
int CircularList<T>::size(){
  return length;
}

template <typename T>
node<T> * CircularList<T>::getList(){
  return tail;
}

template <typename T>
node<T> * CircularList<T>::begin(){
  return tail->next;
}

template <typename T>
node<T> * CircularList<T>::end(){
  return tail;
}

template <typename T>
void CircularList<T>::setLength(int x){
  length = x;
}

template <typename T>
void CircularList<T>::mergeCircularList(CircularList * l){
  if(l->size() > 0){
    if(this->tail == nullptr){
      this->length = l->size();
      this->tail = l->tail;
    }
    else{
      node<T> * lTemp = l->getList(), * ptr;
      ptr = this->tail->next;
      this->tail->next = lTemp->next;   
      lTemp->next = ptr;
      this->length += l->size();
    }
    l->tail = nullptr;
    l->setLength(0);
  }
}

template <typename T>
std::ostream & CircularList<T>::print(std::ostream & os){
  if(length != 0){
    node<T> * temp = tail->next;
    do{
      os << temp->data << " ";
      temp = temp->next;
    } while(temp != tail->next);
  }
  os << std::endl;
  return os;
}

template <typename T>
CircularList<T>::iterator::iterator(node<T> * n) : _it(n){};

template <typename T>
CircularList<T>::iterator::~iterator(){};

template <typename T>
typename CircularList<T>::iterator& CircularList<T>::iterator::operator++(){
  _it = _it->next;
  return *this;
}

template <typename T>
bool CircularList<T>::iterator:: operator ==(node<T> * n) const{
  return (_it == n);
}

template <typename T>
bool CircularList<T>::iterator:: operator !=(node<T> * n) const{
  return (_it != n);
}

template <typename T>
node<T>& CircularList<T>::iterator:: operator *(){
  return *_it;
}
