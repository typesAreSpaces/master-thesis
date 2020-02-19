#include "HornClause.h"

HornClause::HornClause(UnionFind & uf, z3::expr_vector & antecedent, z3::expr & consequent) :
  uf(uf), antecedent(antecedent), consequent(consequent){
}

HornClause::~HornClause(){
}

z3::expr_vector & HornClause::getAntecedent(){
  return antecedent;
}

z3::expr & HornClause::getConsequent(){
  return consequent;
}

bool HornClause::checkTriviality(){
  z3::solver temp_euf_solver(consequent.ctx(), "QF_UF");
  temp_euf_solver.add(z3::mk_and(antecedent));
  temp_euf_solver.add(not(consequent));
  return temp_euf_solver.check() == z3::unsat;
}

bool HornClause::compareEquations(const z3::expr & eq1, const z3::expr & eq2){
  auto f1 = eq1.decl().decl_kind(), f2 = eq2.decl().decl_kind();
  switch(f1){
  case Z3_OP_EQ:
    switch(f2){
    case Z3_OP_EQ:
      return std::min(eq1.arg(0).id(), eq1.arg(1).id()) > std::min(eq2.arg(0).id(), eq2.arg(1).id());
    default:
      throw "Problem @ HornClause::compareEquations. eq2 is not an equality";
    }
  default:
    throw "Problem @ HornClause::compareEquations. eq1 is not an equality";
  }
}

// Removes trivial equalities in the antecedent
// sorting these elements using the following heuristic:
// INSERT-HEURISTIC-DESCRIPTION
void HornClause::normalize(){
  z3::expr_vector aux_z3_vec(consequent.ctx());
  std::vector<z3::expr> aux_vec{};
  unsigned num_terms = antecedent.size();
  for(unsigned i = 0; i < num_terms; i++)
    aux_vec.push_back(antecedent[i]);
  std::sort(aux_vec.begin(), aux_vec.end(), compareEquations);
  antecedent.resize(0);
  for(unsigned i = 0; i < num_terms; i++){
    z3::expr temp_expr = aux_vec[i];
    if(uf.find(temp_expr.arg(0).id()) != uf.find(temp_expr.arg(1).id()))
      antecedent.push_back(temp_expr);
  }
}

// Rearranges a Horn Clauses to the form
// (/\_i u_i = v_i) => a = b, where u_i >= v_i and a >= b
// The < relation on (Term, Term) used is
// defined at Term.cpp
void HornClause::orient(){
  // std::vector<EquationTerm> & antecedent = getAntecedent();
  // EquationTerm & consequent = getConsequent();
  // Term * _u, * _v;
	
  // for(auto & it : antecedent){
  //   _u = it.first, _v = it.second;
  //   if(*_u < *_v)
  //     it = std::make_pair(_v, _u);
  // }
  
  // _u = consequent.first, _v = consequent.second; 
  // if(*_u < *_v)
  //   consequent = std::make_pair(_v, _u);
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
    z3::solver temp_euf_solver(hc1.consequent.ctx(), "QF_UF");
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
