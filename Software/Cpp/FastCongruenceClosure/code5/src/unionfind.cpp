#include "unionfind.h"

UnionFind::UnionFind(int N){
  parent.resize(N);
  rank.resize(N);
  preds.resize(N);
  length = N;
  for(int i = 0; i < N; ++i){
    parent[i] = i;
    rank[i] = 0;
    preds[i] = CircularList<int>();
  }
}

void UnionFind::setPreds(LinkedList & x){
  node * temp = x.getList();
  int vertex, succ;
  vertex = temp->data;
  temp = temp->next;
  while(temp != nullptr){
    succ = temp->data;
    preds[succ].add(vertex);
    temp = temp->next;
  }
}
