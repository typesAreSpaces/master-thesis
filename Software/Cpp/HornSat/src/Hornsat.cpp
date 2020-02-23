#include "Hornsat.h"

// num_dis_pos_literals = number of distinct positive literals in A
// num_basic_horn_clauses = number of basic Horn Clauses in A
Hornsat::Hornsat(std::istream & in) : consistent(true), num_pos(0){
  unsigned input, num_literals, num_hcs;
  in >> num_literals >> num_hcs;

  list_of_literals.resize(num_literals);
  num_args.resize(num_hcs);
  pos_lit_list.resize(num_hcs);
  
  for(unsigned index_hc = 0; index_hc < num_hcs; index_hc++){
    in >> input;
    
    num_args.list_of_clauses[index_hc] = input - 1;
    for(unsigned j = num_args.list_of_clauses[index_hc]; j > 0; --j){
      in >> input;
      addClauseToLiteral(input, index_hc);
    }
    
    in >> input;
    pos_lit_list.list_of_clauses[index_hc] = input;
    // This checks if the Horn Clause is a fact
    if(num_args.list_of_clauses[index_hc] == 0){
      list_of_literals[input].val = true;
      facts.push(index_hc);
      ++num_pos;
    }
  }
}

Hornsat::~Hornsat(){
  Clause * ptr;
  unsigned num_literals = list_of_literals.size();
  for(unsigned i = 0; i < num_literals; ++i){
    ptr = list_of_literals[i].clause_list;
    while(ptr){
      list_of_literals[i].clause_list = list_of_literals[i].clause_list->next;
      delete ptr;
      ptr = list_of_literals[i].clause_list;
    }
  }
}

void Hornsat::addClauseToLiteral(unsigned lit, unsigned clau){
  list_of_literals[lit].clause_list = new Clause(clau, list_of_literals[lit].clause_list);
}

void Hornsat::satisfiable(){
  unsigned clause1, clause2, n, nextpos, oldnumclause = num_pos, newnumclause;
  while(!facts.empty() && consistent){
    newnumclause = 0;
    for(unsigned i = 0; i < oldnumclause && consistent; ++i){
      clause1 = facts.front();
      facts.pop();
      nextpos = pos_lit_list.list_of_clauses[clause1];
      list_of_literals[nextpos];
      Clause * p = list_of_literals[nextpos].clause_list;
      while(p){
	clause2 = p->clause_id;
	--num_args.list_of_clauses[clause2];
	
	if(num_args.list_of_clauses[clause2] == 0){
	  n = pos_lit_list.list_of_clauses[clause2];
	  if(!list_of_literals[n].val){
	    if (n > FALSELITERAL){
	      list_of_literals[n].val = true;
	      facts.push(clause2);
	      ++newnumclause;
	    }
	    else
	      consistent = false;
	  }
	}
	p = p->next;
      }
    }
    oldnumclause = newnumclause;
  }
}

bool Hornsat::isConsistent(){
  return consistent;
}

std::ostream & operator << (std::ostream & os, const Hornsat & hsat){
  os << "Assignments:" << std::endl;
  unsigned _size = hsat.num_args.size();
  for(unsigned i = 0; i < _size; ++i)
    os << "Literal " << i << ": " << hsat.list_of_literals[i].val << std::endl;
  os << "Done";
  return os;
}
