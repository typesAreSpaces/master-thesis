#include "HornClause.h"

HornClause::HornClause(z3::context & ctx, z3::expr_vector antecedent, z3::expr consequent, UnionFindExplain & ufe) :
  ctx(ctx),
  antecedent(antecedent), consequent(consequent), 
  is_common_antecedent(true), num_uncomm_antecedent(0), local_max_lit_id(0)
{

  // ----------------
  normalize(ufe);  //
  orient();        //
  // ----------------

  // ---------------------------------------------------------------
  // This part updates:
  // 1) num_uncomm_antecedent
  // 2) is_common_antecedent
  for(auto hyp : this->antecedent){
    if(local_max_lit_id < hyp.id())
      local_max_lit_id = hyp.id();
    if(!hyp.is_common()){
      num_uncomm_antecedent++;
      is_common_antecedent = false;
    }
  }
  if(local_max_lit_id < this->consequent.id()){
    local_max_lit_id = this->consequent.id();
  }
  // ---------------------------------------------------------------
  return;
}

HornClause::~HornClause(){
#if DEBUG_DESTRUCTOR_HC
  std::cout << "Done ~HornClause" << std::endl;
#endif
}

// Removes trivial equalities in the antecedent
// sorting these elements using the following heuristic:
// HornClause::compareEquation
void HornClause::normalize(UnionFindExplain & ufe){
  std::vector<z3::expr> aux_antecedent ({});

  for(auto expr : antecedent)
    aux_antecedent.push_back(expr);

  std::sort(aux_antecedent.begin(), aux_antecedent.end(), compareEquation);
  antecedent.resize(0);

  for(auto expr : aux_antecedent){
    if(ufe.find(expr.arg(0).id()) != ufe.find(expr.arg(1).id()))
      antecedent.push_back(expr);
  }
  return;
}

// Rearranges a Horn Clauses to the form
// (/\_i u_i = v_i) => a = b, where u_i >= v_i and a >= b
// The < relation on (Term, Term) is HornClause::compareTerm
void HornClause::orient(){

  z3::expr current_lhs(ctx), current_rhs(ctx);

  z3::expr_vector aux_antecedent(ctx);
  for(auto expr : antecedent){
    current_lhs = expr.arg(0), current_rhs = expr.arg(1);
    if(compareTerm(current_lhs, current_rhs))
      aux_antecedent.push_back(current_rhs == current_lhs);
    else
      aux_antecedent.push_back(expr);
  }
  antecedent = aux_antecedent;
  
  std::string consequent_name = consequent.decl().name().str();
  if(consequent_name == "false")
    return;

  current_lhs = consequent.arg(0), current_rhs = consequent.arg(1);
  if(compareTerm(current_lhs, current_rhs))
    consequent = (current_rhs == current_lhs);
  return;
}

bool HornClause::checkTriviality(UnionFindExplain & ufe){
  return ufe.find(consequent.arg(0).id()) == ufe.find(consequent.arg(1).id());
}

const z3::expr_vector & HornClause::getAntecedent() const {
  return antecedent;
}

const z3::expr & HornClause::getConsequent() const {
  return consequent;
}

bool HornClause::isCommonAntecedent() const {
  return is_common_antecedent;
}

bool HornClause::isCommonConsequent() const {
  return consequent.is_common();
}

unsigned HornClause::numUncommAntecedent() const {
  return num_uncomm_antecedent;
}

unsigned HornClause::getLocalMaxLitId() const {
  return local_max_lit_id;
}

// Definition: > \in HornClause \times HornClause -> Bool
// Let hc1 be of the form (/\_{i=0}^m u_i   = v_i  ) => a_1 = a_2
// Let hc2 be of the form (/\_{j=0}^n u_j^' = v_j^') => b_1 = b_2
// hc1 > hc2 iff (repr(a_1) \= repr(a_2)) = (repr(b_1) \= repr(b_2))
//               and (/\_j^n u_j^' = v_j^') => (/\_i^m u_i = v_i_)
//               and n > m
// -------------------------------------------------------------------
bool operator > (HornClause const & hc1, HornClause const & hc2){
  // ------------------------------------------------
  // Precondition:
  // This comparison assumes the consequent of
  // hc1 and hc2 are equal
  // ------------------------------------------------
  assert(hc1.consequent.id() == hc2.consequent.id());

  unsigned num_antecedent_1 = hc1.antecedent.size();
  unsigned num_antecedent_2 = hc2.antecedent.size();

  if(num_antecedent_2 > num_antecedent_1){
    z3::solver temp_euf_solver(hc1.ctx, "QF_UF");
    temp_euf_solver.add(z3::mk_and(hc2.antecedent));
    temp_euf_solver.add(not(z3::mk_and(hc1.antecedent)));
    return temp_euf_solver.check() == z3::unsat;
  }
  return false;
}


z3::expr HornClause::ToZ3Exprc() const{
  return z3::implies(mk_and(antecedent), consequent);
}

bool operator < (const HornClause & hc1, const HornClause & hc2){
  return hc2 > hc1;
}

std::ostream & operator << (std::ostream & os, const HornClause & hc){
  bool first_flag = true;
  unsigned num_antecedent = hc.antecedent.size();
  for(unsigned i = 0; i < num_antecedent; i++){
    if(!first_flag)
      os << " && ";
    first_flag = false;
    os << hc.antecedent[i];
  }
  os << " -> " << hc.consequent;
  return os;
}
