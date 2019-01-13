#include "HornClause.h"

UnionFind HornClause::globalUF = UnionFind();
bool HornClause::change = true;

HornClause::HornClause(UnionFind & uf,
											 std::vector<equality> & antecedent, equality & consequent,
											 std::vector<Vertex*> & terms) :
  localUF(uf), antecedent(antecedent), consequent(consequent){
  antecedentQ = true, consequentQ = true;
  for(auto it = antecedent.begin();
      it != antecedent.end(); ++it){
    antecedentQ = antecedentQ &&
      terms[localUF.find(it->first->getId())]->getSymbolCommonQ() &&
      terms[localUF.find(it->second->getId())]->getSymbolCommonQ();
  }
  consequentQ = consequentQ &&
    terms[localUF.find(consequent.first->getId())]->getSymbolCommonQ() &&
    terms[localUF.find(consequent.second->getId())]->getSymbolCommonQ();
}

HornClause::HornClause(UnionFind & uf, Vertex* u, Vertex* v,
											 std::vector<Vertex*> & terms, bool isDisequation) :
  localUF(uf), antecedentQ(true), consequentQ(true) {
	if(change){
		change = false;
		globalUF = uf;
	}
  unsigned _arity = u->getArity();
  std::vector<Vertex*> & successorsU = u->getSuccessors(),
    & successorsV = v->getSuccessors();
  for(unsigned i = 0; i < _arity; ++i){
    Vertex * _u = terms[localUF.find(successorsU[i]->getId())],
      * _v = terms[localUF.find(successorsV[i]->getId())];
    if(*_u >= *_v)
      antecedent.push_back(std::make_pair(_u, _v));
    else
      antecedent.push_back(std::make_pair(_v, _u));
    antecedentQ = antecedentQ && _u->getSymbolCommonQ() && _v->getSymbolCommonQ();
  }
	if(isDisequation){
		consequent = std::make_pair(terms[Vertex::getTotalNumVertex() - 1],
																terms[Vertex::getTotalNumVertex() - 1]);
		consequentQ = true;
	}
	else{
		  Vertex * _u = terms[localUF.find(u->getId())],
				* _v = terms[localUF.find(v->getId())];
  
			if(*_u >= *_v)
				consequent = std::make_pair(_u, _v);
			else
				consequent = std::make_pair(_v, _u);
			consequentQ = consequentQ && _u->getSymbolCommonQ() && _v->getSymbolCommonQ();
	}
}

HornClause::~HornClause(){
}

// Joins the proper elements to the
// UnionFind data structure
void HornClause::normalize(){
  antecedentQ = true;
  for(std::vector<equality>::iterator it = antecedent.begin();
      it != antecedent.end();){
		//std::cout << "The Equivalence Class" << std::endl;
		//localUF.print(std::cout);
		//std::cout << it->first->getId() << " , " <<  it->second->getId() << std::endl;
		//std::cout << localUF.find(it->first->getId()) << " , " <<  localUF.find(it->second->getId()) << std::endl;
    if(localUF.find(it->first->getId()) == localUF.find(it->second->getId()))
      antecedent.erase(it);
    else{
      localUF.merge(it->first->getId(), it->second->getId());
      antecedentQ = antecedentQ && it->first->getSymbolCommonQ()
				&& it->second->getSymbolCommonQ();
      ++it;
    }
  }
}

bool HornClause::checkTrivial(){
  return (localUF.find(consequent.first->getId()) == localUF.find(consequent.second->getId()));
}

bool HornClause::getAntecedentQ(){
  return antecedentQ;
}
bool HornClause::getConsequentQ(){
  return consequentQ;
}

bool HornClause::getMaximalConsequentQ(){
  return consequent.first->getSymbolCommonQ();
}

std::vector<equality> & HornClause::getAntecedent(){
  return antecedent;
}

equality & HornClause::getConsequent(){
  return consequent;
}

UnionFind & HornClause::getLocalUF(){
  return localUF;
}

UnionFind & HornClause::getGlobalUF(){
  return globalUF;
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

// This comparison assumes the consequent of
// hc1 and hc2 are equal
bool operator > (HornClause & hc1, HornClause & hc2){
	std::vector<equality> & hc1Antecedent = hc1.getAntecedent();
	UnionFind & hc2UF = hc2.getLocalUF();
	for(std::vector<equality>::iterator it = hc1Antecedent.begin();
			it != hc1Antecedent.end(); ++it){

		//std::cout << it->first->getId() << ", " << it->second->getId() << std::endl;
		//std::cout << hc2UF.find(it->first->getId()) << ", " << hc2UF.find(it->second->getId()) << std::endl;
		
		if(hc2UF.find(it->first->getId()) != hc2UF.find(it->second->getId()))
			return false;
	}
	return true;
}

bool operator < (HornClause & hc1, HornClause & hc2){
	return hc2 > hc1;
}


