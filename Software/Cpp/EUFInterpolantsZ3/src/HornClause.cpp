#include "HornClause.h"
#define DEBUG_DESTRUCTOR_HC false

HornClause::HornClause(UnionFind & uf, z3::context & ctx, const unsigned & min_id, z3::expr_vector & subterms,
		       z3::expr_vector antecedent, z3::expr consequent, CCList & cc_list) :
  uf(uf), ctx(ctx), min_id(min_id), subterms(subterms),
  antecedent(antecedent), consequent(consequent), cc_list(cc_list){

  // ---------------------------------------------------------------
  // This part updates subterms in case there are new terms created
  // by a Horn Clause
  for(auto hyp : this->antecedent){
    auto lhs = hyp.arg(0), rhs = hyp.arg(1);
    if(subterms.size() <= hyp.id())
      subterms.resize(hyp.id() + 1);
    subterms.set(hyp.id(), hyp);
    subterms.set(lhs.id(), lhs);
    subterms.set(rhs.id(), rhs);
  }
  if(this->consequent.decl().name().str() == "false"){
    subterms.set(this->consequent.id(), this->consequent);
    return;
  }
  if(subterms.size() <= this->consequent.id())
    subterms.resize(this->consequent.id() + 1);
  
  auto lhs = this->consequent.arg(0), rhs = this->consequent.arg(1);
  subterms.set(this->consequent.id(), this->consequent);
  subterms.set(lhs.id(), lhs);
  subterms.set(rhs.id(), rhs);
  // ---------------------------------------------------------------

  // -------------
  normalize();  //
  orient();     //
  // -------------

  // ---------------------------------------------------------------
  // This part updates subterms (again) in case there are
  // new terms created by a Horn Clause after
  // normalization and orientation
  for(auto hyp : this->antecedent){
    is_common_antecedent = is_common_antecedent && hyp.is_common();
    if(!hyp.is_common())
      num_uncomm_antecedent++;
    auto lhs = hyp.arg(0), rhs = hyp.arg(1);
    if(subterms.size() <= hyp.id()){
      subterms.resize(hyp.id() + 1);
      cc_list.resize(hyp.id() + 1);
    }
    subterms.set(hyp.id(), hyp);
    subterms.set(lhs.id(), lhs);
    subterms.set(rhs.id(), rhs);
    cc_list[lhs.id()].push_back(hyp.id());
    cc_list[rhs.id()].push_back(hyp.id());
  }
  if(this->consequent.decl().name().str() == "false"){
    subterms.set(this->consequent.id(), this->consequent);
    return;
  }
  if(subterms.size() <= this->consequent.id()){
    subterms.resize(this->consequent.id() + 1);
    cc_list.resize(this->consequent.id() + 1);
  }
  
  lhs = this->consequent.arg(0), rhs = this->consequent.arg(1);
  subterms.set(this->consequent.id(), this->consequent);
  subterms.set(lhs.id(), lhs);
  subterms.set(rhs.id(), rhs);
  cc_list[lhs.id()].push_back(this->consequent.id());
  cc_list[rhs.id()].push_back(this->consequent.id());
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
void HornClause::normalize(){
  z3::expr_vector aux_z3_vec(ctx);
  std::vector<z3::expr> aux_vec{};
  unsigned num_terms = antecedent.size();
  for(unsigned i = 0; i < num_terms; i++)
    aux_vec.push_back(antecedent[i]);
  std::sort(aux_vec.begin(), aux_vec.end(), compareEquation);
  antecedent.resize(0);
  for(unsigned i = 0; i < num_terms; i++){
    z3::expr temp_expr = aux_vec[i];
    if(uf.find(temp_expr.arg(0).id()) != uf.find(temp_expr.arg(1).id()))
      antecedent.push_back(temp_expr);
  }
  return;
}

// Rearranges a Horn Clauses to the form
// (/\_i u_i = v_i) => a = b, where u_i >= v_i and a >= b
// The < relation on (Term, Term) is HornClause::compareTerm
void HornClause::orient(){
  z3::expr_vector aux_antecedent(ctx);
  z3::expr current_lhs(ctx), current_rhs(ctx);
  unsigned num = antecedent.size();
  for(unsigned i = 0; i < num; i++){
    current_lhs = antecedent[i].arg(0), current_rhs = antecedent[i].arg(1);
    if(compareTerm(current_lhs, current_rhs))
      aux_antecedent.push_back(current_rhs == current_lhs);
    else
      aux_antecedent.push_back(antecedent[i]);
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

bool HornClause::checkTriviality(){
  return uf.find(consequent.arg(0).id()) == uf.find(consequent.arg(1).id());
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
