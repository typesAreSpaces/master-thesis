#include "Hornsat.h"

unsigned Literal::curr_num_literals = 0;

Hornsat::Hornsat(CongruenceClosureExplain & cce, 
    HornClauses const & hcs) :
  num_hcs(hcs.size()), num_literals(hcs.getMaxLitId()),
  /*This ufe is empty*/ ufe(hcs.getUFESize()), equiv_classes(cce, ufe), 
  list_of_literals(), class_list(),
  num_args(), pos_lit_list(), 
  facts(), to_combine(),
  consistent(true)
{ 

  Literal::curr_num_literals = 0;

  list_of_literals.resize(num_literals + 1);
  class_list      .resize(num_literals + 1);

  num_args    .resize(num_hcs);
  pos_lit_list.resize(num_hcs);

#if DEBUGGING_CONSTRUCTOR
  std::cout << "Horn Clauses processed by Hornsat" << std::endl;
#endif
  ClauseId index_hc = 0;

  for(auto horn_clause : hcs.getHornClauses()){
#if DEBUGGING_CONSTRUCTOR
    std::cout << index_hc << " " << *horn_clause << std::endl;
#endif
    // We only process Horn clauses with uncommon consequent
    if(!horn_clause->isCommonConsequent()){
      // -----------------------------------------------------
      // The following line defines our approach -------------
      // towards conditional elimination
      num_args[index_hc] = horn_clause->numUncommAntecedent();
      // -----------------------------------------------------

      // ------------------------------------------------------
      // Horn clause body processing --------------------------
      // Remark: We only have equations in the antecedent
      for(auto antecedent : horn_clause->getAntecedent()){
#if DEBUGGING_CONSTRUCTOR
        std::cout << "Literals inside antedecent " 
          << antecedent.id() << " " 
          << antecedent << std::endl;
#endif
        Literal * literal = &list_of_literals[antecedent.id()];
        literal->update(antecedent, ufe, index_hc);
        class_list[literal->l_id].emplace_back(literal, LHS);
        class_list[literal->r_id].emplace_back(literal, RHS);
      }
      // ------------------------------------------------------

      // ------------------------------------------------------------
      // Horn clause head processing --------------------------------
      auto consequent = horn_clause->getConsequent();
#if DEBUGGING_CONSTRUCTOR
      std::cout << "Literals inside consequent " 
        << consequent.id() << " " << consequent << std::endl;
#endif
      Literal * literal = 
        &list_of_literals[consequent.decl().name().str() == "false" ?
        FALSELITERAL : consequent.id()];

      pos_lit_list[index_hc] = literal->literal_id;
      if(literal->literal_id > FALSELITERAL){
        literal->update(consequent, ufe);
        class_list[literal->l_id].emplace_back(literal, LHS);
        class_list[literal->r_id].emplace_back(literal, RHS);
      }

      // In the original formulation by Gallier, 
      // this checks if the Horn Clause is a fact,
      // in this approach, this checks if a Horn Clause
      // can be spreading because the its antecedent is
      // common.
      if(num_args[index_hc] == 0){
        literal->val = true;
        facts.push(consequent.id());
        to_combine.push(TermIdPair(
              consequent.arg(0).id(), 
              consequent.arg(1).id()));
        if(literal->literal_id == FALSELITERAL)
          consistent = false;
      }
      // ------------------------------------------------------------
    }
    index_hc++;
  }
#if DEBUGGING_CONSTRUCTOR
  std::cout << "Done @ Hornsat constructor" << std::endl;
#endif
  satisfiable();
}

Hornsat::~Hornsat(){
  for(auto literal : list_of_literals){
    for(auto it = literal.clause_list->begin(); 
        it != literal.clause_list->end(); ){
#if DEBUG_DESTRUCTORS
      std::cout << "Deleting this clause: " << (*it)->clause_id << std::endl;
#endif
      auto first_move_then_delete = it;
      ++it;
      delete *first_move_then_delete;
    }
  }
#if DEBUG_DESTRUCTORS
  std::cout << "Done ~Hornsat" << std::endl;
#endif
}

void Hornsat::satisfiable(){
  LiteralId node;
  while(!facts.empty() && consistent){
    node = facts.front();
    facts.pop();
    for(auto it : *(list_of_literals[node].clause_list)){
      ClauseId clause1 = it->clause_id;
      --num_args[clause1];
      if(num_args[clause1] == 0){
        LiteralId nextnode = pos_lit_list[clause1];
        if(!list_of_literals[nextnode].val){
          if(nextnode){
            facts.push(nextnode);
            list_of_literals[nextnode].val = true;
            TermId u = list_of_literals[nextnode].l_id, 
                   v = list_of_literals[nextnode].r_id;
            //if(equi_classes.areSameClass(u, v)) // FIX: implement areSameClass
            if(true)
              to_combine.push(TermIdPair(u, v));
            
          }
          else
            consistent = false;
        } 
      }
    }
    if(facts.empty() && consistent)
      closure();
  }
}

//std::vector<Replacement> Hornsat::satisfiable(CongruenceClosureExplain & cc){ // TODO: Pay attention to this
//std::vector<Replacement> ans;
//unsigned clause1 = 0, node = 0, nextnode = 0, u = 0, v = 0;

//std::list<unsigned> pending;
//for(auto it = cc.subterms.begin(); it != cc.subterms.end(); ++it)
//if((*it).num_args() > 0)
//pending.push_back(it.getIndex());

//while(!facts.empty() && consistent){
//node = facts.front();
//facts.pop();
//#if DEBUGGING_SATISFIABLE   
//std::cout << "Literal coming from facts: " << node << std::endl;
//std::cout << "Literal coming from facts: " << node << " " << subterms[node] << std::endl;
//std::cout << "Horn clauses such that the node appears in the antecedent:" << std::endl;
//#endif
//auto clause_list_cur_lit = list_of_literals[node].clause_list;
//auto it = clause_list_cur_lit->begin(), end = clause_list_cur_lit->end();
//for(; it != end; ++it){
//clause1 = (*it)->clause_id;
//#if DEBUGGING_SATISFIABLE
//std::cout << "Clause id: " << clause1 << std::endl;
//#endif
//// In this implementation, num_args only decreases
//// if the propagated literal is uncommon
//if(!subterms[node].is_common())
//--num_args[clause1]; 

//// KEEP WORKING HERE (Highest priority)
//// TODO: Capture the propagation
//// ans.push_back(Replacement(clause0, clause1));

//if(num_args[clause1] == 0){
//nextnode = pos_lit_list[clause1];
//if(!list_of_literals[nextnode].val){
//if(nextnode > FALSELITERAL){
//facts.push(nextnode);
//list_of_literals[nextnode].val = true;
//u = list_of_literals[nextnode].l_id,
//v = list_of_literals[nextnode].r_id;
//if(cc.uf.find(u) != cc.uf.find(v))
//update(cc, pending, u, v);
//}
//else
//consistent = false;
//}
//}
//}
//if(facts.empty() && consistent)
//congclosure(cc, pending);
//}
//return ans;
//}
//


void Hornsat::unionupdate(LiteralId x, LiteralId y){ // FIX: almost
  //if(equiv_classes.greater(y, x)){
    //unsigned aux = x;
    //x = y;
    //y = aux;
  //}
  //unsigned repr_x = equiv_classes.find(x), 
           //repr_y = equiv_classes.find(y);
//#if DEBUGGING_UNIONUPDATE
  //std::cout << "Inside unionupdate: " << x << " " << y << std::endl;
//#endif
  //// The next two lines setup an iterate
  //// to go over elements of the class repr_y
  //auto end = equiv_classes.end(repr_y);  
  //for(auto u = equiv_classes.begin(repr_y); u != end; ++u){
    //for(auto p : class_list[*u]){
//#if DEBUGGING_UNIONUPDATE
      //std::cout << "Before, Term: " << *u << " " << p << std::endl;
//#endif
      //if(!p.lit_pointer->val){
        //switch(p.eq_side){
          //case LHS:
            //p.lit_pointer->l_class = repr_x;
            //break;
          //case RHS:
            //p.lit_pointer->r_class = repr_x;
            //break;
        //}
        //if(p.lit_pointer->l_class == p.lit_pointer->r_class){
          //facts.push(p.lit_pointer->literal_id);
          //p.lit_pointer->val= true;
        //}
      //}
//#if DEBUGGING_UNIONUPDATE
      //std::cout << "After,  Term: " << *u << " " << p << std::endl;
//#endif
    //}
  //}
  //equiv_classes.combine(repr_x, repr_y);
}

void Hornsat::closure(){ // FIX: almost
  //while(!to_combine.empty()){
    //auto pair = to_combine.front();
    //to_combine.pop();
    //TermId u = pair.lhs, v = pair.rhs;
    //equiv_classes.combine(u, v, nullptr); // FIX: the nullptr
  //}
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
