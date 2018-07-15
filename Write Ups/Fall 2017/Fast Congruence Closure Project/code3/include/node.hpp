#ifndef NODE_H
#define NODE_H

#include <iostream>
#include <cstddef>

typedef struct node {
  int data;
  struct node * next;
} node;

class linkedList{
private:
  int count;
public:
  node *head, *tail;
  linkedList(){
    head = tail = nullptr;
    count = 0;
  }
  void add(int x){
    node *temp = new node;
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
    ++count;
  }
  int size(){
    return count;
  }
  node * getList(){
    return head;
  }
  void print(){
    node * temp = new node;
    for(temp = head; temp != nullptr; temp = temp->next)
      std::cout << temp->data << " ";
  }
};

class circularList{
private:
  int count;
public:
  node *tail;
  circularList(){
    tail = nullptr;
    count = 0;
  }
  void add(int x){
    if(count == 0)
      addEmpty(x);
    else
      addNonEmpty(x);
    ++count;
  }
  void addEmpty(int x){
    node * temp = new node;
    temp->data = x;
    temp->next = nullptr;
    temp->next = temp;
    tail = temp;
  }
  void addNonEmpty(int x){
    node * temp = new node;
    temp->data = x;
    temp->next = tail->next;
    tail->next = temp;
    tail = temp;
  }
  int size(){
    return count;
  }
  void print(){
    if(count != 0){
      node * temp = tail->next;
      do{
	std::cout << temp->data << " ";
	temp = temp->next;
      } while(temp != tail->next);
    }
  }
};

#endif
