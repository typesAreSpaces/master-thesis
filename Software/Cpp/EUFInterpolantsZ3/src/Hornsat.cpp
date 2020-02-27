#include "Hornsat.h"
#define DEBUGGING_SATISFIABLE false
#define DEBUGGING_UNIONUPDATE false
#define DEBUGGING_CONSTRUCTOR false

unsigned Literal::curr_num_literals = 0;

// // num_dis_pos_literals = number of distinct positive literals in A
// // num_basic_horn_clauses = number of basic Horn Clauses in A
// Hornsat::Hornsat(std::istream & in) : consistent(true), num_pos(0){
//   Literal::curr_num_literals = 0;
//   unsigned input;
//   in >> num_literals >> num_hcs;

//   list_of_literals.resize(num_literals);
//   num_args.resize(num_hcs);
//   pos_lit_list.resize(num_hcs);
  
//   for(unsigned index_hc = 0; index_hc < num_hcs; index_hc++){
//     // The following input represents the number of
//     // antecendents plus 1 (consequent) of a Horn clause (old format)
//     in >> input;

//     // Horn clause body processing
//     num_args[index_hc] = input - 1;
//     for(unsigned j = num_args[index_hc]; j > 0; --j){
//       in >> input;
//       list_of_literals[input].clause_list = list_of_literals[input].clause_list->add(index_hc);
//     }

//     // Horn clause head processing
//     in >> input;
//     pos_lit_list[index_hc] = input;
    
//     // This checks if the Horn Clause is a fact
//     if(num_args[index_hc] == 0){
//       list_of_literals[input].val = true;
//       facts.push(index_hc);
//       ++num_pos;
//       if(input == FALSELITERAL)
// 	consistent = false;
//     }   
//   }
// }

Hornsat::Hornsat(const HornClauses & hcs, UnionFind & uf) :
  subterms(hcs.getSubterms()),
  consistent(true), num_pos(0),
  num_hcs(hcs.size()), num_literals(subterms.size()){
  Literal::curr_num_literals = 0;
  list_of_literals.resize(num_literals);
  class_list.resize(num_literals);
  num_args.resize(num_hcs);
  pos_lit_list.resize(num_hcs);
  
#if DEBUGGING_CONSTRUCTOR
  std::cout << "Horn Clauses processed by Hornsat" << std::endl;
#endif
  unsigned index_hc = 0;
  for(auto horn_clause : hcs.getHornClauses()){
#if DEBUGGING_CONSTRUCTOR
    std::cout << index_hc << " " << *horn_clause << std::endl;
#endif
    // We only process Horn clauses with uncommon consequent
    if(!horn_clause->isCommonConsequent()){      
      // Horn clause body processing
      // Remark: We only have equations in the antecedent
      num_args[index_hc] = horn_clause->numUncommAntecedent();
      for(auto antecedent : horn_clause->getAntecedent()){
#if DEBUGGING_CONSTRUCTOR
	std::cout << "Literals inside antedecent " << antecedent.id() << " " << antecedent << std::endl;
	std::cout << subterms.size() << std::endl;
	assert(antecedent.id() < subterms.size());
#endif
	Literal * literal = &list_of_literals[antecedent.id()];
	literal->l_id = antecedent.arg(0).id();
	literal->r_id = antecedent.arg(1).id();
	literal->l_class = uf.find(literal->l_id);
	literal->r_class = uf.find(literal->r_id);
	literal->clause_list = literal->clause_list->add(index_hc);
	class_list[literal->l_id].emplace_back(literal, LHS);
	class_list[literal->r_id].emplace_back(literal, RHS);
      }

      // Horn clause head processing
      auto consequent = horn_clause->getConsequent();
#if DEBUGGING_CONSTRUCTOR
      std::cout << "Literals inside consequent " << consequent.id() << " " << consequent << std::endl;
#endif
      Literal * literal = &list_of_literals[consequent.decl().name().str() == "false" ?
					    FALSELITERAL :
					    consequent.id()];
      
      pos_lit_list[index_hc] = literal->literal_id;
      if(literal->literal_id > FALSELITERAL){
	literal->l_id = consequent.arg(0).id();
	literal->r_id = consequent.arg(1).id();
	literal->l_class = uf.find(literal->l_id);
	literal->r_class = uf.find(literal->r_id);
	class_list[literal->l_id].emplace_back(literal, LHS);
	class_list[literal->r_id].emplace_back(literal, RHS);
      }

      // This checks if the Horn Clause is a fact
      if(num_args[index_hc] == 0){
	literal->val = true;
	facts.push(index_hc);
	++num_pos;
	if(literal->literal_id == FALSELITERAL)
	  consistent = false;
      }
    }
    index_hc++;
  }
}

Hornsat::~Hornsat(){
  for(auto literal : list_of_literals){
    for(auto it = literal.clause_list->begin(), end = literal.clause_list->end();
	it != end; ++it){
#if DEBUG_DESTRUCTORS
      std::cout << "Deleting this clause: " << (*it)->clause_id << std::endl;
#endif
      delete (*it);
    }
  }
#if DEBUG_DESTRUCTORS
  std::cout << "Done ~Hornsat" << std::endl;
#endif
}

void Hornsat::unionupdate(UnionFind & uf, unsigned x, unsigned y, unsigned clause){
  if(uf.greater(y, x)){
    unsigned aux = x;
    x = y;
    y = aux;
  }
#if DEBUGGING_UNIONUPDATE
  std::cout << "Inside unionupdate: " << x << " " << y << std::endl;
#endif
  auto end = uf.end(y);  
  for(auto u = uf.begin(y); u != end; ++u){
    for(auto p : class_list[*u]){
#if DEBUGGING_UNIONUPDATE
      std::cout << "Before, Term: " << *u << " " << p << std::endl;
#endif
      if(!p.lit_pointer->val){
	switch(p.eq_side){
	case LHS:
	  p.lit_pointer->l_class = x;
	  break;
	case RHS:
	  p.lit_pointer->r_class = x;
	  break;
	}
	if(p.lit_pointer->l_class == p.lit_pointer->r_class){
	  facts.push(clause);
	  p.lit_pointer->val= true;
	}
      }
#if DEBUGGING_UNIONUPDATE
      std::cout << "After,  Term: " << *u << " " << p << std::endl;
#endif
    }
  }
  uf.combine(x, y);
}

void Hornsat::update(CongruenceClosure & cc, std::list<unsigned> & pending, std::queue<unsigned> & facts, unsigned u, unsigned v, unsigned clause){
  // TODO: Implement this
  unionupdate(cc.uf, u, v, clause);
  return;
}

void Hornsat::congclosure(CongruenceClosure & cc, std::list<unsigned> & pending, std::queue<unsigned> & facts){
  // TODO: Implement this
  return;
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

std::vector<Replacement> Hornsat::satisfiable(CongruenceClosure & cc){
  std::vector<Replacement> ans;
  unsigned clause0 = 0, clause1 = 0, node = 0, nextnode = 0, u = 0, v = 0;
  unsigned num_terms = cc.subterms.size();

  std::list<unsigned> pending;
  for(unsigned i = cc.min_id; i < num_terms; i++){
    if(cc.subterms[i].num_args() > 0)
      pending.push_back(i);
  }
  
#if DEBUGGING_SATISFIABLE
  std::cout << "satisfiable using a CongruenceClosure" << std::endl;
  std::cout << "Min ID: " << cc.min_id << " Size: " << num_terms << std::endl;
#endif
  
  while(!facts.empty() && consistent){
    clause0 = facts.front();
    node = pos_lit_list[clause0];
    facts.pop();
#if DEBUGGING_SATISFIABLE   
    std::cout << "Literal coming from facts: " << node << std::endl;
    std::cout << "Literal coming from facts: " << node << " " << subterms[node] << std::endl;
    std::cout << "Horn clauses such that the node appears in the antecedent:" << std::endl;
#endif
    auto clause_list_cur_lit = list_of_literals[node].clause_list;
    auto it = clause_list_cur_lit->begin(), end = clause_list_cur_lit->end();
    for(; it != end; ++it){
      clause1 = (*it)->clause_id;
#if DEBUGGING_SATISFIABLE
      std::cout << "Clause id: " << clause1 << std::endl;
#endif
      --num_args[clause1]; // WRONG: This should decrement only if the clause involved is uncommon
      
      // TODO: Capture the propagation indicated below
      ans.push_back(Replacement(clause0, clause1));
      
      if(num_args[clause1] == 0){
	nextnode = pos_lit_list[clause1];
	if(!list_of_literals[nextnode].val){
	  if(nextnode > FALSELITERAL){
	    facts.push(clause1);
	    list_of_literals[nextnode].val = true;
	    u = list_of_literals[nextnode].l_id,
	      v = list_of_literals[nextnode].r_id;
	    if(cc.uf.find(u) != cc.uf.find(v))
	      update(cc, pending, facts, u, v, clause1);
	  }
	  else
	    consistent = false;
	}
      }
    }
    if(facts.empty() && consistent)
      congclosure(cc, pending, facts);
  }
  return ans;
}

bool Hornsat::isConsistent(){
  return consistent;
}

std::ostream & operator << (std::ostream & os, const Hornsat & hsat){
  for(auto x : hsat.list_of_literals)
    os << "Literal " << x.literal_id
       << " LClass: " << x.l_class
       << " RClass: " << x.r_class
       << " Assigment: " << x.val << std::endl;
  os << "Consistent: " << (hsat.consistent ? "Yes" : "No");
  return os;
}
