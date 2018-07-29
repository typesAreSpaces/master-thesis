#include "HornClause.h"

HornClause::HornClause(UnionFind & uf, Vertex* u, Vertex* v) : localUF(uf) {
  unsigned _arity = u->getArity();
  std::vector<Vertex*> & successorsU = u->getSuccessors(),
    & successorsV = v->getSuccessors();
  for(unsigned i = 0; i < _arity; ++i)
    antecedent.insert(std::make_pair(localUF.find(successorsU[i]->getId()),
				localUF.find(successorsV[i]->getId())));
  consequent = std::make_pair(localUF.find(u->getId()),
			 localUF.find(v->getId()));
}

HornClause::~HornClause(){
}

void HornClause::normalize(){
  for(std::set<equality>::iterator it = antecedent.begin();
      it != antecedent.end(); ++it){
    if(localUF.find(it->first) == localUF.find(it->second))
      antecedent.erase(*it);
    else
      localUF.merge(it->first, it->second);
  }
}

bool HornClause::checkTrivial(){
  if(localUF.find(consequent.first) == localUF.find(consequent.second))
    return true;
  return false;
}

std::ostream & operator << (std::ostream & os, HornClause & hc){
  bool flag = true;
  for(std::set<equality>::iterator it = hc.antecedent.begin(); it != hc.antecedent.end(); ++it){
    if(flag)
      os << it->first << "=" << it->second;
    else
      os << "," <<  it->first << "=" << it->second;
    flag = false;
  }
  os << "->" << hc.consequent.first << "=" << hc.consequent.second;
  return os;
}
