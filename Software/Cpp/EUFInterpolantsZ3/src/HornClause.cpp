#include "HornClause.h"
#define DEBUG_DESTRUCTOR_HC false

HornClause::HornClause(z3::context & ctx, z3::expr_vector antecedent, z3::expr consequent, UnionFindExplain & ufe) :
  ctx(ctx),
  antecedent(antecedent), consequent(consequent){

  // ----------------
  normalize(ufe);  //
  orient();        //
  // ----------------

  // ---------------------------------------------------------------
  // This part updates:
  // 1) num_uncomm_antecedent
  // 2) is_common_antecedent
  for(auto hyp : this->antecedent)
    if(!hyp.is_common()){
      num_uncomm_antecedent++;
      is_common_antecedent = false;
    }
  // ---------------------------------------------------------------
  return;
}

HornClause::~HornClause(){
#if DEBUG_DESTRUCTOR_HC
  std::cout << "Done ~HornClause" << std::endl;
#endif
}

bool HornClause::compareEquation(const z3::expr & eq1, const z3::expr & eq2){
  switch(eq1.decl().decl_kind()){
  case Z3_OP_EQ:
    switch(eq2.decl().decl_kind()){
    case Z3_OP_EQ:
      return std::min(eq1.arg(0).id(), eq1.arg(1).id()) > std::min(eq2.arg(0).id(), eq2.arg(1).id()); // <--- Heuristic
    default:
      throw "Problem @ HornClause::compareEquation. eq2 is not an equality";
    }
  default:
    throw "Problem @ HornClause::compareEquation. eq1 is not an equality";
  }
}

// Read it as: compareTerm(t1, t2) iff t2 is 'better than' t1
bool HornClause::compareTerm(const z3::expr & t1, const z3::expr & t2){
  if (t1.is_common() != t2.is_common()){
    return t1.is_common() < t2.is_common();
  }
  else{
    unsigned arity1 = t1.num_args(), arity2 = t2.num_args();
    if(arity1 != arity2){
      // Because we prefer a term with fewer arity
      return arity1 > arity2;
    }
    else{
      // Because we prefer a term with smaller id
      return t1.id() > t2.id();
    }
  }
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

bool HornClause::isCommonAntecedent(){
  return is_common_antecedent;
}

bool HornClause::isCommonConsequent(){
  return consequent.is_common();
}

unsigned HornClause::numUncommAntecedent(){
  return num_uncomm_antecedent;
}

// Definition: > \in HornClause \times HornClause
// Let hc1 be of the form (/\_{i=0}^m u_i   = v_i  ) => a_1 = a_2
// Let hc2 be of the form (/\_{j=0}^n u_j^' = v_j^') => b_1 = b_2
// hc1 > hc2 iff (repr(a_1) \= repr(a_2)) = (repr(b_1) \= repr(b_2))
//               and (/\_j^n u_j^' = v_j^') => (/\_i^m u_i = v_i_)
//               and n > m
// -------------------------------------------------------------------
bool operator > (const HornClause & hc1, const HornClause & hc2){
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
