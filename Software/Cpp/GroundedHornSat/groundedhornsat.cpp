#include <iostream>
#include <queue>
#define MAX 100

typedef struct clause{
  int clauseno;
  struct clause * next;
} clause;

typedef struct literal{
  bool val;
  struct clause * clauselist;
} literal;

typedef struct Hornclause{
  literal listOfLiterals[MAX];
} Hornclause;

typedef struct count{
  int listOfClauses[MAX];
} count;
  
typedef std::queue<int> queuei;

void addClauseToLiteral(Hornclause &, int, int);
void initialize(Hornclause &, int, int, int &, count &, count &, queuei &);
void satisfiable(Hornclause &, queuei &, bool &, int, count &, count &);

int main(){
  // k = number of distinct positive literals in A
  // m = number of basic Horn Clauses in A
  int k, m, numpos = 0;
  bool consistent = true;
  count numargs, poslitlist;
  Hornclause A;
  queuei Queue;

  std::cin >> k >> m;
  
  initialize(A, k, m, numpos, numargs, poslitlist, Queue);
  
  satisfiable(A, Queue, consistent, numpos, numargs, poslitlist);

  if(consistent){
    std::cout << "Satisfiable Horn Clause\nAssignment:" << std::endl;
    for(int i = 1; i <= k; ++i)
      std::cout << "Literal " << i << ": " << A.listOfLiterals[i].val << std::endl;
  }
  else
    std::cout << "Unsatisfiable Horn Clause" << std::endl;

  return 0;
}

void addClauseToLiteral(Hornclause &a, int lit, int clau){
  clause * p = new clause;
  p->clauseno = clau;
  p->next = a.listOfLiterals[lit].clauselist;
  a.listOfLiterals[lit].clauselist = p;
}

void initialize(Hornclause &a, int k, int m, int &numpos, count &numargs, count &poslitlist, queuei &q){
  int s, temp;

  for(int i = 1; i <= k; ++i)
    a.listOfLiterals[i] = (literal) {false, NULL};

  for(int i = 1; i <= m; ++i){
    std::cin >> s;
    numargs.listOfClauses[i] = s - 1;
    int j = s - 1;
    while(j > 0){
      std::cin >> temp;
      addClauseToLiteral(a, temp, i);
      --j;
    }
    std::cin >> temp;
    poslitlist.listOfClauses[i] = temp;
    if(s == 1){
      a.listOfLiterals[temp].val = true;
      q.push(i);
      ++numpos;
    }
  }
}

void satisfiable(Hornclause &a, queuei &q, bool &consistent, int numpos, count &numargs, count &poslitlist){
  int clause1, clause2, n, nextpos, oldnumclause = numpos, newnumclause;
  while(!q.empty() && consistent){
    newnumclause = 0;
    for(int i = 1; i <= oldnumclause && consistent; ++i){
      clause1 = q.front();
      q.pop();
      nextpos = poslitlist.listOfClauses[clause1];
      clause * p = a.listOfLiterals[nextpos].clauselist;
      for(; p != NULL; p = p->next){
	clause2 = p->clauseno;
	--numargs.listOfClauses[clause2];
	if(numargs.listOfClauses[clause2] == 0){
	  n = poslitlist.listOfClauses[clause2];
	  if(!a.listOfLiterals[n].val){
	    if (n != 0){
	      a.listOfLiterals[n].val = true;
	      q.push(clause2);
	    }
	    else
	      consistent = false;
	  }
	}
      }
    }
  }
}
