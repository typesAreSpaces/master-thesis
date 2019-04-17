#include "HornClause.h"

UnionFind HornClause::global_UF               = UnionFind();
bool HornClause::is_first_time                = true;
std::vector<Vertex*> HornClause::global_terms = std::vector<Vertex*>();

HornClause::HornClause(UnionFind & uf,
					   std::vector<equality> & antecedent,
					   equality & consequent,
					   std::vector<Vertex*> & terms) :
  local_UF(uf),
  antecedent(antecedent),
  consequent(consequent){
  if(is_first_time){
	is_first_time = false;
	global_UF = uf;
	global_terms = terms;
  }
  antecedent_boolean_value = true, consequent_boolean_value = true;
  for(auto it = antecedent.begin();
      it != antecedent.end(); ++it){
    antecedent_boolean_value = antecedent_boolean_value &&
	  getVertex(it->first)->getSymbolCommonQ() &&
	  getVertex(it->second)->getSymbolCommonQ();
  }
  consequent_boolean_value = consequent_boolean_value &&		
	getVertex(consequent.first)->getSymbolCommonQ() &&
	getVertex(consequent.second)->getSymbolCommonQ();
  }

// It's assumed the arities of Vertex * u,
// Vertex * v are the same
HornClause::HornClause(UnionFind & uf,
					   Vertex* u, Vertex* v,
					   std::vector<Vertex*> & terms,
					   bool is_disequation) :
  local_UF(uf),
  antecedent_boolean_value(true),
  consequent_boolean_value(true){
  if(is_first_time){
	is_first_time = false;
	global_UF = uf;
	global_terms = terms;
  }
	
  unsigned _arity = u->getArity();
  assert(_arity == v->getArity());
  std::vector<Vertex*> & successors_u = u->getSuccessors(),
    & successors_v = v->getSuccessors();
  for(unsigned i = 0; i < _arity; ++i){
	Vertex * _u = getVertex(successors_u[i]),
      * _v = getVertex(successors_v[i]);
    if(*_u >= *_v)
      antecedent.push_back(std::make_pair(_u, _v));
    else
      antecedent.push_back(std::make_pair(_v, _u));
    antecedent_boolean_value = antecedent_boolean_value
	  && _u->getSymbolCommonQ() && _v->getSymbolCommonQ();
  }
  if(is_disequation){
	consequent = std::make_pair(terms[Vertex::getTotalNumVertex() - 1],
								terms[Vertex::getTotalNumVertex() - 1]);
	consequent_boolean_value = true;
  }
  else{
	Vertex * _u = getVertex(u),
	  * _v = getVertex(v);
  
	if(*_u >= *_v)
	  consequent = std::make_pair(_u, _v);
	else
	  consequent = std::make_pair(_v, _u);
	consequent_boolean_value = consequent_boolean_value
	  && _u->getSymbolCommonQ() && _v->getSymbolCommonQ();
  }
}

HornClause::~HornClause(){
}

// Joins the proper elements to the
// UnionFind data structure
void HornClause::normalize(){
  antecedent_boolean_value = true;
  for(std::vector<equality>::iterator it = antecedent.begin();
      it != antecedent.end();){
    if(getVertex(it->first) == getVertex(it->second))
      antecedent.erase(it);
    else{
      local_UF.merge(it->first->getId(), it->second->getId());
      antecedent_boolean_value = antecedent_boolean_value
		&& it->first->getSymbolCommonQ()
		&& it->second->getSymbolCommonQ();
      ++it;
    }
  }
}

bool HornClause::checkTriviality(){
  return (getVertex(consequent.first) == getVertex(consequent.second));
}

bool HornClause::getAntecedentValue(){
  return antecedent_boolean_value;
}
bool HornClause::getConsequentValue(){
  return consequent_boolean_value;
}

bool HornClause::getMaximalConsequent(){
  return consequent.first->getSymbolCommonQ();
}

std::vector<equality> & HornClause::getAntecedent(){
  return antecedent;
}

equality & HornClause::getConsequent(){
  return consequent;
}

UnionFind & HornClause::getLocalUF(){
  return local_UF;
}

UnionFind & HornClause::getGlobalUF(){
  return global_UF;
}

Vertex * HornClause::getVertex(unsigned i){
  return global_terms[local_UF.find(i)];
}

Vertex * HornClause::getVertex(Vertex * v){
  return global_terms[local_UF.find(v->getId())];
}

// This comparison assumes the consequent of
// hc1 and hc2 are equal
// If it finds an element in the antecedent of hc1
// but not in the antecedent of hc2, then the
// operator returns false, true otherwise
bool operator > (HornClause & hc1, HornClause & hc2){
  std::vector<equality> & hc1Antecedent = hc1.getAntecedent();
  UnionFind & hc2UF = hc2.getLocalUF();
  for(std::vector<equality>::iterator it = hc1Antecedent.begin();
	  it != hc1Antecedent.end(); ++it)
	if(hc2UF.find(it->first->getId()) != hc2UF.find(it->second->getId()))
	  return false;
  return true;
}

bool operator < (HornClause & hc1, HornClause & hc2){
  return hc2 > hc1;
}

std::ostream & operator << (std::ostream & os, HornClause & hc){
  bool flag = true;
  for(std::vector<equality>::iterator it = hc.antecedent.begin();
	  it != hc.antecedent.end(); ++it){
    if(flag)
      os << it->first->to_string() << " = " << it->second->to_string();
    else
      os << " && " <<  it->first->to_string() << " = " << it->second->to_string();
    flag = false;
  }
  os << " -> " << hc.consequent.first->to_string()
	 << " = " << hc.consequent.second->to_string();
  return os;
}
