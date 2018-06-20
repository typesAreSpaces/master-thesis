#ifndef UNIONFIND_H
#define UNIONFIND_H

#include <vector>
#include "node.hpp"

class UF{
private:
  std::vector<int> parent, rank;
  std::vector<circularList> preds;
  int count;
public:
  UF(int N){
    parent.resize(N);
    rank.resize(N);
    preds.resize(N);
    count = N;
    for(int i = 0; i < N; ++i){
      parent[i] = i;
      rank[i] = 0;
      preds[i] = circularList();
    }
  }
  void setPreds(linkedList x){
    node * temp = x.getList();
    int fname, fsig;
    fname = temp->data;
    temp = temp->next;
    while(temp != nullptr){
      fsig = temp->data;
      preds[fsig].add(fname);
      temp = temp->next;
    }
  }
  void addPred(int x, int y){
    preds[x].add(y);
  }
  void merge(int x, int y, int lx, int ly){
    link(find(x), find(y), lx, ly);
    --count;
  }
  void link(int x, int y, int lx, int ly){
    if(rank[x] >= rank[y] || lx >= ly)
      parent[y] = x;
    else{
      parent[x] = y;
      if(rank[x] == rank[y])
	++rank[y];
    }
  }
  int find(int x){
    if(parent[x] != x)
      parent[x] = find(parent[x]);
    return parent[x];
  }
  circularList list(int x){
    return preds[x];
  }
  int getRank(int x){
    return rank[find(x)];
  }
  int size(){
    return count;
  }
};

#endif
