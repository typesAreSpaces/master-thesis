#include "HornClause.h"

// It's assumed the arities of Term * u,
// Term * v are the same
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
  
  for(unsigned index = 0; index < _arity; ++index){

    iterator_lhs = cc.getReprTerm(successors_u[index]);
    iterator_rhs = cc.getReprTerm(successors_v[index]);
    
    if(*iterator_lhs >= *iterator_rhs)
      antecedent.push_back(std::make_pair(iterator_lhs, iterator_rhs));
    else
      antecedent.push_back(std::make_pair(iterator_rhs, iterator_lhs));
    
    is_antecedent_common = is_antecedent_common
      && iterator_lhs->getSymbolCommonQ() && iterator_rhs->getSymbolCommonQ();
  }
  
  if(is_disequation){
    consequent = std::make_pair(cc.getOriginalTerm(0),
				cc.getOriginalTerm(0));
    is_consequent_common = true;
  }
  else{
    iterator_lhs = cc.getReprTerm(u);
    iterator_rhs = cc.getReprTerm(v);
  
    if(*iterator_lhs >= *iterator_rhs)
      consequent = std::make_pair(iterator_lhs, iterator_rhs);
    else
      consequent = std::make_pair(iterator_rhs, iterator_lhs);
    is_consequent_common = is_consequent_common
      && iterator_lhs->getSymbolCommonQ() && iterator_rhs->getSymbolCommonQ();
  }

  // Normalization needed here
  
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

  // Normalization needed here
  
  this->local_equiv_class = cc.getDeepEquivalenceClass();
}

HornClause::~HornClause(){
}

// Joins the proper elements to the
// UnionFind data structure
// - If the elements are equal then
//   'normalize' removes them from 'antecedent'
// - Otherwise, it adds them in the congruence
void HornClause::normalize(CongruenceClosure & cc){
  // TODO: Check if this doesn't go out of bound
  is_antecedent_common = true;
  for(auto it = antecedent.begin(); it != antecedent.end(); ++it){
    if(cc.getReprTerm(it->first) == cc.getReprTerm(it->second))
      antecedent.erase(it);
    else{
      cc.merge(it->first->getId(), it->second->getId()); // This is wrong
      is_antecedent_common = is_antecedent_common
	&& it->first->getSymbolCommonQ()
	&& it->second->getSymbolCommonQ();
      ++it; // <- Specially here
    }
  }
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

// This comparison assumes the consequent of
// hc1 and hc2 are equal
// If it finds an element in the antecedent of hc1
// but not in the antecedent of hc2, then the
// operator returns false, true otherwise
bool operator > (HornClause & hc1, HornClause & hc2){

  std::vector<EquationTerm> & hc1Antecedent = hc1.getAntecedent();
  UnionFind & hc2UF = hc2.getLocalUF();
  
  for(auto it : hc1Antecedent)
    if(hc2UF.find(it.first->getId()) != hc2UF.find(it.second->getId()))
      return false;
  return true;
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
