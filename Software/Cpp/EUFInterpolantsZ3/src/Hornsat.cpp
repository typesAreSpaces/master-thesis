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
    num_args[index_hc] = input - 1;
    for(unsigned j = num_args[index_hc]; j > 0; --j){
      in >> input;
      list_of_literals[input].clause_list = list_of_literals[input].clause_list->add(index_hc);
    }

    // Horn clause head processing
    in >> input;
    pos_lit_list[index_hc] = input;
    
    // This checks if the Horn Clause is a fact
    if(num_args[index_hc] == 0){
      list_of_literals[input].val = true;
      facts.push(index_hc);
      ++num_pos;
      if(input == FALSELITERAL)
	consistent = false;
    }   
  }
}

Hornsat::Hornsat(const HornClauses & hcs) : consistent(true), num_pos(0){
  unsigned num_hcs = hcs.size(), num_literals = hcs.maxID();
  list_of_literals.resize(num_literals);
  classlist.resize(num_literals);
  num_args.resize(num_hcs);
  pos_lit_list.resize(num_hcs);
  
  unsigned index_hc = 0;
  for(auto horn_clause : hcs.getHornClauses()){
    // We only process Horn clauses with uncommon consequent
    if(!horn_clause->isCommonConsequent()){
      // Horn clause body processing
      // Remark: We only have equations in the antecedent
      num_args[index_hc] = horn_clause->numUncommAntecedent();
      for(auto antecedent : horn_clause->getAntecedent()){       
	Literal * literal = &list_of_literals[antecedent.id()];
	literal->lclass = antecedent.arg(0).id();
	classlist[literal->lclass].push_back(&literal->lclass);
	literal->rclass = antecedent.arg(1).id();
	classlist[literal->rclass].push_back(&literal->rclass);
	literal->clause_list = literal->clause_list->add(index_hc);
      }

      // Horn clause head processing
      auto consequent = horn_clause->getConsequent();
      Literal * literal = &list_of_literals[consequent.decl().name().str() == "false" ? FALSELITERAL : consequent.id()];
    
      if(literal->literal_id == 0)
	pos_lit_list[index_hc] = FALSELITERAL;
      else{
	pos_lit_list[index_hc] = consequent.id();
	literal->lclass = consequent.arg(0).id();
	classlist[literal->lclass].push_back(&literal->lclass);
	literal->rclass = consequent.arg(1).id();
	classlist[literal->rclass].push_back(&literal->rclass);
      }

      // This checks if the Horn Clause is a fact
      if(num_args[index_hc] == 0){
	literal->val = true;
	facts.push(index_hc);
	++num_pos;
	if(literal->literal_id == 0)
	  consistent = false;
      }
    }
    index_hc++;
  }
}

Hornsat::~Hornsat(){
  for(auto literal : list_of_literals){
    for(auto it = literal.clause_list->begin(), end = literal.clause_list->end();
	it != end; ++it)
      delete (*it);    
  }
}

void Hornsat::unionupdate(UnionFind & uf, unsigned x, unsigned y){
  unsigned aux;
  if(uf.greater(y, x)){
    aux = x;
    x = y;
    y = aux;
  }
  uf.merge(x, y);
  for(auto u : uf.getEquivClass(y)){
    for(auto p : classlist[u]){
      std::cout << *p << std::endl;
    }
  }
}

void Hornsat::satisfiable(){
  unsigned clause1 = 0, clause2 = 0, literal = 0, nextpos = 0, newnumclause = 0, oldnumclause = num_pos;
  while(!facts.empty() && consistent){
    newnumclause = 0;
    for(unsigned i = 0; i < oldnumclause && consistent; ++i){
      clause1 = facts.front();
      facts.pop();
      nextpos = pos_lit_list[clause1];
      auto clause_list_cur_lit = list_of_literals[nextpos].clause_list;
      auto it = clause_list_cur_lit->begin(), end = clause_list_cur_lit->end();
      for(; it != end; ++it){
	clause2 = (*it)->clause_id;
	--num_args[clause2];
	if(num_args[clause2] == 0){
	  literal = pos_lit_list[clause2];
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

void Hornsat::satisfiable(UnionFind & uf){
  unsigned clause1 = 0, node = 0, nextnode = 0, u = 0, v = 0;
  while(!facts.empty() && consistent){
    node = facts.front();
    facts.pop();
    auto clause_list_cur_lit = list_of_literals[node].clause_list;
    auto it = clause_list_cur_lit->begin(), end = clause_list_cur_lit->end();
    for(; it != end; ++it){
      clause1 = (*it)->clause_id;
      --num_args[clause1];
      if(num_args[clause1] == 0){
	nextnode = pos_lit_list[clause1];
	if(!list_of_literals[nextnode].val){
	  if(nextnode > FALSELITERAL){
	    facts.push(nextnode);
	    list_of_literals[nextnode].val = true;
	    u = list_of_literals[nextnode].lclass, v = list_of_literals[nextnode].rclass;
	    if(uf.find(u) != uf.find(v))
	      std::cout << "Missing implementation 1" << std::endl;
	      // Something else with u, v, FIND(u, R), FIND(v, R)
	  }
	  else
	    consistent = false;
	}
      }
    }
    if(facts.empty() && consistent)
      std::cout << "Missing implementation 2" << std::endl;
      // closure();
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
    os << "Literal " << x.literal_id
       << " LClass: " << x.lclass
       << " RClass: " << x.rclass
       << " Assigment: " << x.val << std::endl;
  os << "Consistent: " << (hsat.consistent ? "Yes" : "No");
  return os;
}
