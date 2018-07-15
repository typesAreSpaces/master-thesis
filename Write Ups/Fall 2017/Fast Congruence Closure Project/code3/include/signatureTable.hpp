#ifndef SIG_TABLE_H
#define SIG_TABLE_H

#include <vector>
#include <map>
#include <utility>
#include "node.hpp"

typedef std::map<int, int > tree;
typedef std::map<std::pair<int, int>, int> treePairs;

class signatureTable{
private:
public:
  //table1 :: Signatures -> Names
  tree table1;
  //table2 :: Signatures x Signatures -> Names
  treePairs table2;
  signatureTable(){
  }
  void enter(linkedList x){
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
  }
  void remove(linkedList x){
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
  }
  int query(linkedList x){
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
  }
};

#endif
