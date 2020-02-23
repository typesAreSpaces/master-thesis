#include "Hornsat.h"

unsigned Literal::curr_num_literals = 0;

// num_dis_pos_literals = number of distinct positive literals in A
// num_basic_horn_clauses = number of basic Horn Clauses in A
Hornsat::Hornsat(std::istream & in) : consistent(true), num_pos(0){
  unsigned input, num_literals, num_hcs;
  in >> num_literals >> num_hcs;

  list_of_literals.resize(num_literals);
  num_args.resize(num_hcs);
  pos_lit_list.resize(num_hcs);
  
  for(unsigned index_hc = 0; index_hc < num_hcs; index_hc++){
    // The following input represents the number of antecendents plus 1 (consequent) of a Horn clause (old format)
    in >> input;

    // Horn clause body processing
    num_args.insert(index_hc, input - 1);
    for(unsigned j = num_args.get(index_hc); j > 0; --j){
      in >> input;
      list_of_literals[input].clause_list = list_of_literals[input].clause_list->add(index_hc);
    }

    // Horn clause head processing
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
  for(auto literal : list_of_literals){
    for(auto it = literal.clause_list->begin(), end = literal.clause_list->end();
	it != end; ++it)
      delete (*it);    
  }
}

void Hornsat::satisfiable(){
  unsigned clause1 = 0, clause2 = 0, literal = 0, nextpos = 0, newnumclause = 0, oldnumclause = num_pos;
  while(!facts.empty() && consistent){
    newnumclause = 0;
    for(unsigned i = 0; i < oldnumclause && consistent; ++i){
      clause1 = facts.front();
      facts.pop();
      nextpos = pos_lit_list.list_of_clauses[clause1];
      auto clause_list_cur_lit = list_of_literals[nextpos].clause_list;
      auto it = clause_list_cur_lit->begin(), end = clause_list_cur_lit->end();
      for(; it != end; ++it){
	clause2 = (*it)->clause_id;
	--num_args.list_of_clauses[clause2];
	if(num_args.list_of_clauses[clause2] == 0){
	  literal = pos_lit_list.list_of_clauses[clause2];
	  if(!list_of_literals[literal].val){
	    if (literal > FALSELITERAL){
	      list_of_literals[literal].val = true;
	      facts.push(clause2);
	      ++newnumclause;
	    }
	    else
	      consistent = false;
	  }
	}
      }
    }
    oldnumclause = newnumclause;
  }
}

bool Hornsat::isConsistent(){
  return consistent;
}

std::ostream & operator << (std::ostream & os, const Hornsat & hsat){
  // unsigned _size = hsat.list_of_literals.size();
  // for(unsigned i = 0; i < _size; ++i)
  //   os << "Literal " << i << ": " << hsat.list_of_literals[i].val << std::endl;

  for(auto x : hsat.list_of_literals)
    os << "Literal " << x.literal_id << " Assigment: " << x.val << std::endl;
  os << "Done";
  return os;
}
