#include <iostream>
#include "node.h"


LinkedList::LinkedList(){
  this->head = this->tail = nullptr;
  this->count = 0;
}

void LinkedList::add(int x){
  node * temp = new node;
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
  ++this->count;
}

int LinkedList::size(){
  return this->count;
}

node * LinkedList::getList(){
  return this->head;
}

ostream & LinkedList:: print(ostream & os){
  node * temp = new node;
  for(temp = head; temp != nullptr; temp = temp->next)
    os << temp->data << " ";
  os << std::endl;
  return os;
}

CircularList::CircularList(){
  tail = nullptr;
  count = 0;
}

void CircularList::add(int x){
  if(count == 0)
    addEmpty(x);
  else
    addNonEmpty(x);
  ++count;
}

void CircularList::addEmpty(int x){
  node * temp = new node;
  temp->data = x;
  temp->next = nullptr;
  temp->next = temp;
  tail = temp;
}

void CircularList::addNonEmpty(int x){
  node * temp = new node;
  temp->data = x;
  temp->next = tail->next;
  tail->next = temp;
  tail = temp;
}

int CircularList::size(){
  return count;
}

std::ostream & CircularList::print(std::ostream & os){
  if(count != 0){
    node * temp = tail->next;
    do{
      os << temp->data << " ";
      temp = temp->next;
    } while(temp != tail->next);
  }
  os << std::endl;
  return os;
}

int main(){
  return 0;
}
