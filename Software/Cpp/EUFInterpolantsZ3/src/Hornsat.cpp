#include "Hornsat.h"
#define DEBUGGING_SATISFIABLE 1
#define DEBUGGING_UNIONUPDATE 1
#define DEBUGGING_CONSTRUCTOR 1

unsigned Literal::curr_num_literals = 0;

Hornsat::Hornsat(Z3Subterms const & subterms, UnionFindExplain & ufe, 
    HornClauses const & hcs) :
  subterms(subterms),
  consistent(true), num_pos(0),
  num_hcs(hcs.size()), num_literals(subterms.size())
{ 

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
        std::cout << "Literals inside antedecent " 
          << antecedent.id() << " " 
          << antecedent << std::endl;
        std::cout << subterms.size() << std::endl;
#endif
        Literal * literal = &list_of_literals[antecedent.id()];
        literal->l_id = antecedent.arg(0).id();
        literal->r_id = antecedent.arg(1).id();
        literal->l_class = ufe.find(literal->l_id);
        literal->r_class = ufe.find(literal->r_id);
        literal->clause_list = literal->clause_list->add(index_hc);
        class_list[literal->l_id].emplace_back(literal, LHS);
        class_list[literal->r_id].emplace_back(literal, RHS);
      }

      // Horn clause head processing
      auto consequent = horn_clause->getConsequent();
#if DEBUGGING_CONSTRUCTOR
      std::cout << "Literals inside consequent " 
        << consequent.id() << " " << consequent << std::endl;
#endif
      Literal * literal = &list_of_literals[consequent.decl().name().str() == "false" ?
        FALSELITERAL :
        consequent.id()];

      pos_lit_list[index_hc] = literal->literal_id;
      if(literal->literal_id > FALSELITERAL){
        literal->l_id = consequent.arg(0).id();
        literal->r_id = consequent.arg(1).id();
        literal->l_class = ufe.find(literal->l_id);
        literal->r_class = ufe.find(literal->r_id);
        class_list[literal->l_id].emplace_back(literal, LHS);
        class_list[literal->r_id].emplace_back(literal, RHS);
      }

      // This checks if the Horn Clause is a fact
      if(num_args[index_hc] == 0){
        literal->val = true;
        facts.push(consequent.id());
        ++num_pos;
        if(literal->literal_id == FALSELITERAL)
          consistent = false;
      }
    }
    index_hc++;
  }
#if DEBUGGING_CONSTRUCTOR
      std::cout << "Done" << std::endl;
#endif
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

void Hornsat::unionupdate(UnionFindExplain & ufe,
    unsigned x, unsigned y){
  if(ufe.greater(y, x)){
    unsigned aux = x;
    x = y;
    y = aux;
  }
  unsigned repr_x = ufe.find(x), repr_y = ufe.find(y);
#if DEBUGGING_UNIONUPDATE
  std::cout << "Inside unionupdate: " << x << " " << y << std::endl;
#endif
  // The next two lines setup an iterate
  // to go over elements of the class repr_y
  auto end = ufe.end(repr_y);  
  for(auto u = ufe.begin(repr_y); u != end; ++u){
    for(auto p : class_list[*u]){
#if DEBUGGING_UNIONUPDATE
      std::cout << "Before, Term: " << *u << " " << p << std::endl;
#endif
      if(!p.lit_pointer->val){
        switch(p.eq_side){
          case LHS:
            p.lit_pointer->l_class = repr_x;
            break;
          case RHS:
            p.lit_pointer->r_class = repr_x;
            break;
        }
        if(p.lit_pointer->l_class == p.lit_pointer->r_class){
          facts.push(p.lit_pointer->literal_id);
          p.lit_pointer->val= true;
        }
      }
#if DEBUGGING_UNIONUPDATE
      std::cout << "After,  Term: " << *u << " " << p << std::endl;
#endif
    }
  }
  ufe.combine(repr_x, repr_y);
}

void Hornsat::update(CongruenceClosureExplain & cc, std::list<unsigned> & pending,
    unsigned v, unsigned w){
  // TODO: Implement this
  //unsigned aux_var;

  //// Invariant: v is always the repr
  //if(cc.pred_list[cc.uf.find(v)].size() < cc.pred_list[cc.uf.find(w)].size()){
    //aux_var = v;
    //v = w;
    //w = aux_var;
  //}
  //if(compareTerm(subterms[cc.uf.find(v)], subterms[cc.uf.find(w)])){
    //aux_var = v;
    //v = w;
    //w = aux_var;
  //}

  //for(auto u : cc.pred_list[cc.uf.find(w)]){
    //cc.sig_table.erase(subterms[u]);
    //pending.push_back(u);
  //}
  //unionupdate(cc.uf, v, w);
  //cc.pred_list[cc.uf.find(v)].splice(cc.pred_list[cc.uf.find(v)].end(), cc.pred_list[cc.uf.find(w)]);

  return;
}

void Hornsat::congclosure(CongruenceClosureExplain & cc, std::list<unsigned> & pending){
  std::list<std::pair<unsigned, unsigned> > combine;

  while(!pending.empty()){
    combine.clear();
    for(auto v_id : pending){
      const z3::expr & v = subterms[v_id];
      try{
        auto w_id = cc.sig_table.query(v);
        combine.push_back(std::make_pair(v_id, w_id));
      }
      catch(...){
        cc.sig_table.enter(v);
      }
    }
    pending.clear();
    for(auto v_w : combine){
      unsigned v = v_w.first, w = v_w.second;
      if(cc.uf.find(v) != cc.uf.find(w))
        update(cc, pending, v, w);
    }
  }
  return;
}

// void Hornsat::satisfiable(){
//   unsigned clause1 = 0, clause2 = 0, literal = 0, nextpos = 0, newnumclause = 0, oldnumclause = num_pos;
//   while(!facts.empty() && consistent){
//     newnumclause = 0;
//     for(unsigned i = 0; i < oldnumclause && consistent; ++i){
//       clause1 = facts.front();
//       facts.pop();
//       nextpos = pos_lit_list[clause1];
//       auto clause_list_cur_lit = list_of_literals[nextpos].clause_list;
//       auto it = clause_list_cur_lit->begin(), end = clause_list_cur_lit->end();
//       for(; it != end; ++it){
// 	clause2 = (*it)->clause_id;
// 	--num_args[clause2];
// 	if(num_args[clause2] == 0){
// 	  literal = pos_lit_list[clause2];
// 	  if(!list_of_literals[literal].val){
// 	    if (literal > FALSELITERAL){
// 	      list_of_literals[literal].val = true;
// 	      facts.push(clause2);
// 	      ++newnumclause;
// 	    }
// 	    else
// 	      consistent = false;
// 	  }
// 	}
//       }
//     }
//     oldnumclause = newnumclause;
//   }
// }

std::vector<Replacement> Hornsat::satisfiable(CongruenceClosureExplain & cc){
  std::vector<Replacement> ans;
  unsigned clause1 = 0, node = 0, nextnode = 0, u = 0, v = 0;

  std::list<unsigned> pending;
  for(auto it = cc.subterms.begin(); it != cc.subterms.end(); ++it)
    if((*it).num_args() > 0)
      pending.push_back(it.getIndex());

  while(!facts.empty() && consistent){
    node = facts.front();
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
      // In this implementation, num_args only decreases
      // if the propagated literal is uncommon
      if(!subterms[node].is_common())
        --num_args[clause1]; 

      // KEEP WORKING HERE (Highest priority)
      // TODO: Capture the propagation
      // ans.push_back(Replacement(clause0, clause1));

      if(num_args[clause1] == 0){
        nextnode = pos_lit_list[clause1];
        if(!list_of_literals[nextnode].val){
          if(nextnode > FALSELITERAL){
            facts.push(nextnode);
            list_of_literals[nextnode].val = true;
            u = list_of_literals[nextnode].l_id,
              v = list_of_literals[nextnode].r_id;
            if(cc.uf.find(u) != cc.uf.find(v))
              update(cc, pending, u, v);
          }
          else
            consistent = false;
        }
      }
    }
    if(facts.empty() && consistent)
      congclosure(cc, pending);
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
