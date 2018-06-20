#include <iostream>
using namespace std;

// k := number of Clauses
int k;

char mapping(int k){
  switch(k){
  case 1: return 'a';
  case 2: return 'b';
  case 3: return 'f';
  case 4: return 'P';
  case 5: return 'Q';
  case 6: return 'R';
  }
}

int main(){
  cin >> k;
  
  return 0;
}
