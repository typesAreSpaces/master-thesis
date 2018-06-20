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
      int fname, fsig1;
      node * temp = x.getList();
      fname = temp->data;
      temp = temp->next;
      fsig1 = temp->data;
      table1[fsig1] = fname;
    }
    if(x.size() == 3){
      int fname, fsig1, fsig2;
      node * temp = x.getList();
      fname = temp->data;
      temp = temp->next;
      fsig1 = temp->data;
      temp = temp->next;
      fsig2 = temp->data;
      table2[std::make_pair(fsig1, fsig2)] = fname;
    }
  }
  void remove(linkedList x){
    if(x.size() == 2){
      int fname, fsig1;
      node * temp = x.getList();
      fname = temp->data;
      temp = temp->next;
      fsig1 = temp->data;
      if(query(x) != -1)
	table1.erase(fsig1);
    }
    if(x.size() == 3){
      int fname, fsig1, fsig2;
      node * temp = x.getList();
      fname = temp->data;
      temp = temp->next;
      fsig1 = temp->data;
      temp = temp->next;
      fsig2 = temp->data;
      if(query(x) != -1)
	table2.erase(std::make_pair(fsig1, fsig2));
    }
  }
  int query(linkedList x){
    if(x.size() == 2){
      int fname, fsig1;
      node * temp = x.getList();
      fname = temp->data;
      temp = temp->next;
      fsig1 = temp->data;
      tree::iterator it = table1.find(fsig1);
      if(it == table1.end())
	return -1;
      else
	return table1.find(fsig1)->second;
    }
    if(x.size() == 3){
      int fname, fsig1, fsig2;
      node * temp = x.getList();
      fname = temp->data;
      temp = temp->next;
      fsig1 = temp->data;
      temp = temp->next;
      fsig2 = temp->data;
      treePairs::iterator it = table2.find(std::make_pair(fsig1, fsig2));
      if(it == table2.end()){
	return -1;
      }
      else
	return table2.find(std::make_pair(fsig1, fsig2))->second;
    }
    // This case is unreachable,
    // nonetheless, the compiler doesn't complain
    else
      return -1;
  }
};

#endif
