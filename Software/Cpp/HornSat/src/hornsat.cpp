#include "hornsat.h"

// numDisPosLiterals = number of distinct positive literals in A
// numBasicHornClauses = number of basic Horn Clauses in A
Hornclause::Hornclause(std::istream & in){
  int input;
  this->consistent = true;
  this->numpos = 0;
  in >> this->numDisPosLiterals >> this->numBasicHornClauses;

  for(int i = 1; i <= this->numDisPosLiterals; ++i)
    this->listOfLiterals[i] = (literal) {false, NULL};
  
  for(int i = 1; i <= this->numBasicHornClauses; ++i){
    in >> input;
    this->numargs.listOfClauses[i] = input - 1;
    for(int j = this->numargs.listOfClauses[i]; j > 0; --j){
      in >> input;
      this->addClauseToLiteral(input, i);
    }
    in >> input;
    this->poslitlist.listOfClauses[i] = input;
    // This checks if the Horn Clause is a fact
    if(this->numargs.listOfClauses[i] == 0){
      this->listOfLiterals[input].val = true;
      this->q.push(i);
      ++this->numpos;
    }
  }
}

Hornclause::~Hornclause(){
  clause * ptr;
  for(int i = 1; i <= this->numBasicHornClauses; ++i){
    ptr = this->listOfLiterals[i].clauselist;
    while(ptr){
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
  int clause1, clause2, n, nextpos,
    oldnumclause = this->numpos, newnumclause;
  while(!this->q.empty() && this->consistent){
    newnumclause = 0;
    for(int i = 1; i <= oldnumclause && this->consistent; ++i){
      clause1 = this->q.front();
      this->q.pop();
      nextpos = this->poslitlist.listOfClauses[clause1];
      for(clause * p = this->listOfLiterals[nextpos].clauselist;
	  p != NULL;
	  p = p->next){
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

std::ostream & Hornclause::printAssignment(std::ostream & os){
  os << "Assignment:" << std::endl;
  for(int i = 1; i <= this->numDisPosLiterals; ++i)
    os << "Literal " << i << ": " << this->listOfLiterals[i].val << std::endl;
  return os;
}
