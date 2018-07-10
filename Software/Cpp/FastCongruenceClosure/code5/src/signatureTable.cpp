#include "signatureTable.h"

SignatureTable::SignatureTable(){}

SignatureTable::~SignatureTable(){}

void SignatureTable::enter(Vertex* v){
  /*
  int _arity = v->getArity();
  if(_arity == 1){
    table1.insert(signatureArg1())
  }
  if(_arity == 2){
  }
  
  if(x.size() == 2){
    int vertex, succ1;
    node * temp = x.getList();
    vertex = temp->data;
    succ1 = temp->next->data;
    table1[succ1] = vertex;
  }
  if(x.size() == 3){
    int vertex, succ1, succ2;
    node * temp = x.getList();
    vertex = temp->data;
    succ1 = temp->next->data;
    succ2 = temp->next->next->data;
    table2[std::make_pair(succ1, succ2)] = vertex;
  }
  */
  return;
}

void SignatureTable::remove(Vertex * v){
  /*
  if(x.size() == 2){
    int vertex, succ1;
    node * temp = x.getList();
    vertex = temp->data;
    succ1 = temp->next->data;
    if(query(x) != -1)
      table1.erase(succ1);
  }
  if(x.size() == 3){
    int vertex, succ1, succ2;
    node * temp = x.getList();
    vertex = temp->data;
    succ1 = temp->next->data;
    succ2 = temp->next->next->data;
    if(query(x) != -1)
      table2.erase(std::make_pair(succ1, succ2));
  }
  */
  return;
}

Vertex * SignatureTable::query(Vertex * v){
  /*
  if(x.size() == 2){
    int vertex, succ1;
    node * temp = x.getList();
    vertex = temp->data;
    succ1 = temp->next->data;
    tree::iterator it = table1.find(succ1);
    if(it == table1.end())
      return -1;
    else
      return table1.find(succ1)->second;
  }
  if(x.size() == 3){
    int vertex, succ1, succ2;
    node * temp = x.getList();
    vertex = temp->data;
    succ1 = temp->next->data;
    succ2 = temp->next->next->data;
    treePairs::iterator it = table2.find(std::make_pair(succ1, succ2));
    if(it == table2.end())
      return -1;
    else
      return table2.find(std::make_pair(succ1, succ2))->second;
  }
  // This case is unreachable,
  // Nonetheless, the compiler complains otherwise
  else{
    std::cout << "Wait what?" << std::endl;
    return -1;
  }
  */
  return v;
}
