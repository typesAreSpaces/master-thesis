#include "HornClause.h"

HornClause::HornClause(UnionFind & uf, Vertex* u, Vertex* v,
		       std::vector<Vertex*> & terms) :
  localUF(uf), antecedentQ(true), consequentQ(true) {
  unsigned _arity = u->getArity();
  std::vector<Vertex*> & successorsU = u->getSuccessors(),
    & successorsV = v->getSuccessors();
  for(unsigned i = 0; i < _arity; ++i){
    antecedent.push_back(std::make_pair(terms[localUF.find(successorsU[i]->getId())],
					terms[localUF.find(successorsV[i]->getId())]));
    antecedentQ = antecedentQ && terms[localUF.find(successorsU[i]->getId())]->getSymbolCommonQ();
    antecedentQ = antecedentQ && terms[localUF.find(successorsV[i]->getId())]->getSymbolCommonQ();
  }
  if(terms[localUF.find(u->getId())]->getSymbolCommonQ())
    consequent = std::make_pair(terms[localUF.find(v->getId())],
				terms[localUF.find(u->getId())]);
  else
    consequent = std::make_pair(terms[localUF.find(u->getId())],
				terms[localUF.find(v->getId())]);
  consequentQ = consequentQ && terms[localUF.find(u->getId())]->getSymbolCommonQ();
  consequentQ = consequentQ && terms[localUF.find(v->getId())]->getSymbolCommonQ();
}

HornClause::~HornClause(){
}

void HornClause::normalize(){
  antecedentQ = true;
  for(std::vector<equality>::iterator it = antecedent.begin();
      it != antecedent.end();){
    if(localUF.find(it->first->getId()) == localUF.find(it->second->getId()))
      antecedent.erase(it);
    else{
      localUF.merge(it->first->getId(), it->second->getId());
      antecedentQ = antecedentQ && it->first->getSymbolCommonQ();
      antecedentQ = antecedentQ && it->second->getSymbolCommonQ();
      ++it;
    }
  }
}

bool HornClause::checkTrivial(){
  if(localUF.find(consequent.first->getId()) == localUF.find(consequent.second->getId()))
    return true;
  return false;
}

bool HornClause::getAntecedentQ(){
  return antecedentQ;
}
bool HornClause::getConsequentQ(){
  return consequentQ;
}

std::ostream & operator << (std::ostream & os, HornClause & hc){
  bool flag = true;
  for(std::vector<equality>::iterator it = hc.antecedent.begin(); it != hc.antecedent.end(); ++it){
    if(flag)
      os << it->first->to_string() << " = " << it->second->to_string();
    else
      os << " && " <<  it->first->to_string() << " = " << it->second->to_string();
    flag = false;
  }
  os << " -> " << hc.consequent.first->to_string() << " = " << hc.consequent.second->to_string();
  return os;
}
