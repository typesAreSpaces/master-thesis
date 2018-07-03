#include "hornsat.h"

Hornclause::Hornclause(int numDisPosLiterals, int numBasicHornClauses){
  int s, temp;
  this->consistent = true;
  this->numpos = 0;
  this->numDisPosLiterals = numDisPosLiterals;
  this->numBasicHornClauses = numBasicHornClauses;

  for(int i = 1; i <= this->numDisPosLiterals; ++i)
    this->listOfLiterals[i] = (literal) {false, NULL};
  
  for(int i = 1; i <= this->numBasicHornClauses; ++i){
    std::cin >> s;
    this->numargs.listOfClauses[i] = s - 1;
    int j = s - 1;
    while(j > 0){
      std::cin >> temp;
      this->addClauseToLiteral(temp, i);
      --j;
    }
    std::cin >> temp;
    this->poslitlist.listOfClauses[i] = temp;
    if(s == 1){
      this->listOfLiterals[temp].val = true;
      this->q.push(i);
      ++this->numpos;
    }
  }
}

Hornclause::~Hornclause(){
  clause * ptr;
  for(int i = 1; i <= this->numBasicHornClauses; ++i){
    ptr = this->listOfLiterals[i].clauselist;
    while(this->listOfLiterals[i].clauselist){
      this->listOfLiterals[i].clauselist = this->listOfLiterals[i].clauselist->next;
      delete ptr;
      ptr = this->listOfLiterals[i].clauselist;
    }
  }
}

void Hornclause::addClauseToLiteral(int lit, int clau){
  clause * p = new clause;
  p->clauseno = clau;
  p->next = this->listOfLiterals[lit].clauselist;
  this->listOfLiterals[lit].clauselist = p;
}

void Hornclause::satisfiable(){
  int clause1, clause2, n, nextpos, oldnumclause = this->numpos, newnumclause;
  while(!this->q.empty() && this->consistent){
    newnumclause = 0;
    for(int i = 1; i <= oldnumclause && this->consistent; ++i){
      clause1 = this->q.front();
      this->q.pop();
      nextpos = this->poslitlist.listOfClauses[clause1];
      clause * p = this->listOfLiterals[nextpos].clauselist;
      for(; p != NULL; p = p->next){
	clause2 = p->clauseno;
	--this->numargs.listOfClauses[clause2];
	if(this->numargs.listOfClauses[clause2] == 0){
	  n = this->poslitlist.listOfClauses[clause2];
	  if(!this->listOfLiterals[n].val){
	    if (n != 0){
	      this->listOfLiterals[n].val = true;
	      this->q.push(clause2);
	      ++newnumclause;
	    }
	    else
	      this->consistent = false;
	  }
	}
      }
    }
    oldnumclause = newnumclause;
  }  
}

bool Hornclause::isConsistent(){
  return this->consistent;
}


void Hornclause::printAssignment(){
  std::cout << "Assignment:" << std::endl;
  for(int i = 1; i <= this->numDisPosLiterals; ++i)
    std::cout << "Literal " << i << ": " << this->listOfLiterals[i].val << std::endl;
}
