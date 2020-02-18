#include "HornClause.h"

HornClause::HornClause(z3::expr_vector const & antecedent, z3::expr const & consequent) :
  antecedent(antecedent), consequent(consequent){
}

HornClause::~HornClause(){
}

z3::expr_vector const & HornClause::getAntecedent(){
  return antecedent;
}

z3::expr const & HornClause::getConsequent(){
  return consequent;
}

// UnionFind & HornClause::getLocalUF(){
//   return local_equiv_class;
// }

bool HornClause::checkTriviality(){
  z3::solver temp_euf_solver(consequent.ctx(), "QF_UF");
  temp_euf_solver.add(z3::mk_and(antecedent));
  temp_euf_solver.add(not(consequent));
  return temp_euf_solver.check() == z3::unsat;
}

// Removes trivial equalities in the antecedent
// sorting these elements using the following heuristic:
// INSERT-HEURISTIC-DESCRIPTION
void HornClause::normalize(){
  // std::sort(antecedent.begin(), antecedent.end(), compareEquations); // <- Heuristic
  // for(auto equation = antecedent.begin(); equation != antecedent.end();){
  //   if(!cc.areEqual(equation->first, equation->second)){
  //     cc.addEquation(equation->first, equation->second);
  //     ++equation;
  //   }
  //   else
  //     equation = antecedent.erase(equation);
  // }
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

// -------------------------------------------------------------------
// Precondition (?):
// This comparison assumes the consequent of
// hc1 and hc2 are equal
// -------------------------------------------------------------------
// Definition: > \in HornClause \times HornClause
// Let hc1 = (/\_i^m u_i = v_i) => a_1 = a_2
// Let hc2 = (/\_j^n u_j^' = v_j^') => b_1 = b_2
// hc1 > hc2 iff (repr(a_1) = repr(a_2)) = (repr(b_1) = repr(b_2))
//               and (/\_j^n u_j^' = v_j^') => (/\_i^m u_i = v_i_)
//               and n > m
// -------------------------------------------------------------------
bool operator > (const HornClause & hc1, const HornClause & hc2){
  assert(hc1.consequent.id() == hc2.consequent.id());  

  unsigned num_antecedent_1 = hc1.antecedent.size();
  unsigned num_antecedent_2 = hc2.antecedent.size();

  if(hc1.consequent.id() == hc2.consequent.id()
     && num_antecedent_2 > num_antecedent_1){
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
  bool flag = true;
  unsigned num_antecedent = hc.antecedent.size();
  for(unsigned i = 0; i < num_antecedent; i++){
    os << hc.antecedent[i];
    if(!flag)
      os << " && ";
    flag = false;
  }
  os << hc.consequent;
  return os;
}
