#include "HornClause.h"

// HornClause produces a horn clause for the form
// /\_i repr(u_i) = repr(v_i) => repr(f(u_1, ..., u_n)) = repr(f(v_1, ..., v_n))
// such that Term u = f(u_1, ..., u_n), Term v = f(v_1, ..., v_n)
// It's assumed the arities of Term * u,
// Term * v are the same (also their signatures ...)
HornClause::HornClause(CongruenceClosure & cc,
		       Term * u, Term * v,
		       bool is_disequation) :
  is_antecedent_common(true),
  is_consequent_common(true)
{
  Term * iterator_lhs, * iterator_rhs;
  
  unsigned _arity = u->getArity();
  assert(_arity == v->getArity());
  const std::vector<Term*> & successors_u = u->getSuccessors(),
    & successors_v = v->getSuccessors();

  // ---------------------------------------------
  // This part effectively orients the Horn Clause
  for(unsigned index_arity = 0; index_arity < _arity; ++index_arity){

    iterator_lhs = cc.getReprTerm(successors_u[index_arity]);
    iterator_rhs = cc.getReprTerm(successors_v[index_arity]);
    
    if(*iterator_lhs >= *iterator_rhs)
      antecedent.push_back(std::make_pair(iterator_lhs, iterator_rhs));
    else
      antecedent.push_back(std::make_pair(iterator_rhs, iterator_lhs));
    
    is_antecedent_common = is_antecedent_common
      && iterator_lhs->getSymbolCommonQ() && iterator_rhs->getSymbolCommonQ();
  }
  // ---------------------------------------------
  
  if(is_disequation){
    consequent = std::make_pair(cc.getOriginalTerm(0),
				cc.getOriginalTerm(0));
    is_consequent_common = true;
  }
  else{
    iterator_lhs = cc.getReprTerm(u);
    iterator_rhs = cc.getReprTerm(v);
    // ---------------------------------------------
    // This part effectively orients the Horn Clause
    if(*iterator_lhs >= *iterator_rhs)
      consequent = std::make_pair(iterator_lhs, iterator_rhs);
    else
      consequent = std::make_pair(iterator_rhs, iterator_lhs);
    // ---------------------------------------------
    is_consequent_common = is_consequent_common
      && iterator_lhs->getSymbolCommonQ() && iterator_rhs->getSymbolCommonQ();
  }

  // -------------------------------------------------------------------------------
  // Normalization
  std::sort(antecedent.begin(), antecedent.end(), compareEquations); // <- Heuristic
  for(auto equation = antecedent.begin(); equation != antecedent.end();){
    if(!cc.areEqual(equation->first, equation->second)){
      cc.addEquation(equation->first, equation->second);
      ++equation;
    }
    else
      equation = antecedent.erase(equation);
  }
  // -------------------------------------------------------------------------------
  
  this->local_equiv_class = cc.getDeepEquivalenceClass();
}
  
HornClause::HornClause(CongruenceClosure & cc,
		       std::vector<EquationTerm> & antecedent,
		       EquationTerm & consequent) :
  is_antecedent_common(true),
  is_consequent_common(true),
  antecedent(antecedent),
  consequent(consequent)
{
  for(auto it : antecedent){
    is_antecedent_common = is_antecedent_common &&
      cc.getReprTerm(it.first)->getSymbolCommonQ() &&
      cc.getReprTerm(it.second)->getSymbolCommonQ();
  }
  is_consequent_common = is_consequent_common &&		
    cc.getReprTerm(consequent.first)->getSymbolCommonQ() &&
    cc.getReprTerm(consequent.second)->getSymbolCommonQ();
  
  orient();

  // -------------------------------------------------------------------------------
  // Normalization
  std::sort(antecedent.begin(), antecedent.end(), compareEquations); // <- Heuristic
  for(auto equation = antecedent.begin(); equation != antecedent.end();){
    if(!cc.areEqual(equation->first, equation->second)){
      cc.addEquation(equation->first, equation->second);
      ++equation;
    }
    else
      equation = antecedent.erase(equation);
  }
  // -------------------------------------------------------------------------------
  
  this->local_equiv_class = cc.getDeepEquivalenceClass();
}

HornClause::~HornClause(){
}

bool HornClause::checkTriviality(){
  return (local_equiv_class.find(consequent.first->getId())
	  == local_equiv_class.find(consequent.second->getId()));
}

bool HornClause::getAntecedentCommon(){
  return is_antecedent_common;
}
bool HornClause::getConsequentCommon(){
  return is_consequent_common;
}

bool HornClause::getMaximalConsequent(){
  return consequent.first->getSymbolCommonQ();
}

std::vector<EquationTerm> & HornClause::getAntecedent(){
  return antecedent;
}

EquationTerm & HornClause::getConsequent(){
  return consequent;
}

UnionFind & HornClause::getLocalUF(){
  return local_equiv_class;
}


// Rearranges a Horn Clauses to the form
// (/\_i u_i = v_i) => a = b, where u_i >= v_i and a >= b
// The < relation on (Term, Term) used is
// defined at Term.cpp
void HornClause::orient(){
  
  std::vector<EquationTerm> & antecedent = getAntecedent();
  EquationTerm & consequent = getConsequent();
  Term * _u, * _v;
	
  for(auto & it : antecedent){
    _u = it.first, _v = it.second;
    if(*_u < *_v)
      it = std::make_pair(_v, _u);
  }
  
  _u = consequent.first, _v = consequent.second; 
  if(*_u < *_v)
    consequent = std::make_pair(_v, _u);
}

bool HornClause::compareEquations(const EquationTerm & eq1, const EquationTerm & eq2){
  return std::min(eq1.first->getLength(), eq1.second->getLength())
    > std::min(eq2.first->getLength(), eq2.second->getLength());
}

// -------------------------------------------------------------------
// Precondition:
// This comparison assumes the consequent of
// hc1 and hc2 are equal
// -------------------------------------------------------------------
// Definition: > \in HornClause \times HornClause
// Let hc1 = (/\_i^m u_i = v_i) => a_1 = a_2
// Let hc2 = (/\_j^n u_j^' = v_j^') => b_1 = b_2
// hc1 > hc2 iff (/\_j^n u_j^' = v_j^') => (/\_i^m u_i = v_i_)
//               and (repr(a_1) = repr(a_2)) = (repr(b_1) = repr(b_2))
//               and n > m
// -------------------------------------------------------------------
// If it finds an element in the antecedent of hc1
// but not in the antecedent of hc2, then the
// operator returns false, true otherwise
// -------------------------------------------------------------------
bool operator > (HornClause & hc1, HornClause & hc2){

  std::vector<EquationTerm> & hc1Antecedent = hc1.getAntecedent();
  UnionFind & hc2UF = hc2.getLocalUF();
  
  for(auto it : hc1Antecedent)
    if(hc2UF.find(it.first->getId()) != hc2UF.find(it.second->getId()))
      return false;
  return hc1Antecedent.size() > hc2.getAntecedent().size();
}

bool operator < (HornClause & hc1, HornClause & hc2){
  return hc2 > hc1;
}

std::ostream & operator << (std::ostream & os, const HornClause & hc){
  bool flag = true;
  for(auto it : hc.antecedent){
    if(flag)
      os << it.first->to_string() << " = " << it.second->to_string();
    else
      os << " && " <<  it.first->to_string() << " = " << it.second->to_string();
    flag = false;
  }
  os << " -> " << hc.consequent.first->to_string()
     << " = " << hc.consequent.second->to_string();
  return os;
}
