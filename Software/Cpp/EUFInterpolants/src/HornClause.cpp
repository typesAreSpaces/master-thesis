#include "HornClause.h"

// It's assumed the arities of Term * u,
// Term * v are the same
HornClause::HornClause(CongruenceClosure & cc,
		       Term* u, Term* v,
		       bool is_disequation) :
  is_antecedent_common(true),
  is_consequent_common(true),
  local_cc(cc)
{
  Term * iterator_lhs, * iterator_rhs;
  
  unsigned _arity = u->getArity();
  assert(_arity == v->getArity());
  
  const std::vector<Term*> & successors_u = u->getSuccessors(),
    & successors_v = v->getSuccessors();
  
  for(unsigned index = 0; index < _arity; ++index){

    iterator_lhs = local_cc.getReprTerm(successors_u[index]);
    iterator_rhs = local_cc.getReprTerm(successors_v[index]);
    
    if(*iterator_lhs >= *iterator_rhs)
      antecedent.push_back(std::make_pair(iterator_lhs, iterator_rhs));
    else
      antecedent.push_back(std::make_pair(iterator_rhs, iterator_lhs));
    
    is_antecedent_common = is_antecedent_common
      && iterator_lhs->getSymbolCommonQ() && iterator_rhs->getSymbolCommonQ();
  }
  
  if(is_disequation){
    consequent = std::make_pair(local_cc.getOriginalTerm(0),
				local_cc.getOriginalTerm(0));
    is_consequent_common = true;
  }
  else{
    iterator_lhs = local_cc.getReprTerm(u);
    iterator_rhs = local_cc.getReprTerm(v);
  
    if(*iterator_lhs >= *iterator_rhs)
      consequent = std::make_pair(iterator_lhs, iterator_rhs);
    else
      consequent = std::make_pair(iterator_rhs, iterator_lhs);
    is_consequent_common = is_consequent_common
      && iterator_lhs->getSymbolCommonQ() && iterator_rhs->getSymbolCommonQ();
  }
}
  
HornClause::HornClause(CongruenceClosure & cc,
		       std::vector<EquationTerm> & antecedent,
		       EquationTerm & consequent) :
  is_antecedent_common(true),
  is_consequent_common(true),
  local_cc(cc),
  antecedent(antecedent),
  consequent(consequent)
{
  for(auto it : antecedent){
    is_antecedent_common = is_antecedent_common &&
      local_cc.getReprTerm(it.first)->getSymbolCommonQ() &&
      local_cc.getReprTerm(it.second)->getSymbolCommonQ();
  }
  is_consequent_common = is_consequent_common &&		
    local_cc.getReprTerm(consequent.first)->getSymbolCommonQ() &&
    local_cc.getReprTerm(consequent.second)->getSymbolCommonQ();
}

HornClause::~HornClause(){
}

// Joins the proper elements to the
// UnionFind data structure
void HornClause::normalize(){
  // TODO: Check if this doesn't go out of bound
  is_antecedent_common = true;
  for(auto it = antecedent.begin(); it != antecedent.end(); ++it){
    if(local_cc.getReprTerm(it->first) == local_cc.getReprTerm(it->second))
      antecedent.erase(it);
    else{
      local_cc.merge(it->first->getId(), it->second->getId()); // This is wrong
      is_antecedent_common = is_antecedent_common
	&& it->first->getSymbolCommonQ()
	&& it->second->getSymbolCommonQ();
      ++it; // <- Specially here
    }
  }
}

bool HornClause::checkTriviality(){
  return (local_cc.getReprTerm(consequent.first) == local_cc.getReprTerm(consequent.second));
}

bool HornClause::getAntecedentValue(){
  return is_antecedent_common;
}
bool HornClause::getConsequentValue(){
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

// // This comparison assumes the consequent of
// // hc1 and hc2 are equal
// // If it finds an element in the antecedent of hc1
// // but not in the antecedent of hc2, then the
// // operator returns false, true otherwise
// bool operator > (HornClause & hc1, HornClause & hc2){

//   std::vector<EquationTerm> & hc1Antecedent = hc1.getAntecedent();
//   UnionFind & hc2UF = hc2.getLocalUF();
  
//   for(auto it : hc1Antecedent)
//     if(hc2UF.find(it.first->getId()) != hc2UF.find(it.second->getId()))
//       return false;
//   return true;
// }

// bool operator < (HornClause & hc1, HornClause & hc2){
//   return hc2 > hc1;
// }

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
