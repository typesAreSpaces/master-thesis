#include "HornClauses.h"

unsigned HornClauses::numHornClauses = 0;

HornClauses::HornClauses(){
}

HornClauses::~HornClauses(){
  for(std::vector<HornClause*>::iterator it = hornClausesType1.begin();
      it != hornClausesType1.end(); ++it)
    delete *it;
  for(std::vector<HornClause*>::iterator it = hornClausesType2.begin();
      it != hornClausesType2.end(); ++it)
    delete *it;
  for(std::vector<HornClause*>::iterator it = hornClausesType2_1.begin();
      it != hornClausesType2_1.end(); ++it)
    delete *it;
  for(std::vector<HornClause*>::iterator it = hornClausesType3.begin();
      it != hornClausesType3.end(); ++it)
    delete *it;
  for(std::vector<HornClause*>::iterator it = hornClausesType4.begin();
      it != hornClausesType4.end(); ++it)
    delete *it;
}

void HornClauses::addHornClause(UnionFind & uf, Vertex* u, Vertex* v, std::vector<Vertex*> & terms){
  HornClause * hc = new HornClause(uf, u, v, terms);
  hc->normalize();
  if(hc->checkTrivial())
    delete hc;
  if(hc->getAntecedentQ()){
    if(hc->getConsequentQ())
      hornClausesType1.push_back(hc);
    else{
      if(!hc->getMaximalConsequentQ())
	hornClausesType2_1.push_back(hc);
      else
	hornClausesType2.push_back(hc);
    }
  }
  else{
    if(hc->getConsequentQ())
      hornClausesType3.push_back(hc);
    else
      hornClausesType4.push_back(hc);
  }
  ++numHornClauses;
}

//TODO: Complete this method
void HornClauses::conditionalElimination(){
  unsigned l = hornClausesType2.size();
  while(l > 0){
    HornClause * _temp = hornClausesType2[l - 1];
    hornClausesType2.erase(--hornClausesType2.end());
    --l;

    for(std::vector<HornClause*>::iterator it = hornClausesType2.begin();
	it != hornClausesType2.end(); ++it){
      
    }
    for(std::vector<HornClause*>::iterator it = hornClausesType3.begin();
	it != hornClausesType3.end(); ++it){
      
    }
    for(std::vector<HornClause*>::iterator it = hornClausesType4.begin();
	it != hornClausesType4.end(); ++it){
      
    }
    delete _temp;
  }
}

std::ostream & operator << (std::ostream & os, HornClauses & hcs){
  std::cout << "Type 1" << std::endl;
  for(std::vector<HornClause*>::iterator it = hcs.hornClausesType1.begin();
      it != hcs.hornClausesType1.end(); ++it)
    os << **it << std::endl;
  std::cout << "Type 2" << std::endl;
  for(std::vector<HornClause*>::iterator it = hcs.hornClausesType2.begin();
      it != hcs.hornClausesType2.end(); ++it)
    os << **it << std::endl;
  std::cout << "Type 2_1" << std::endl;
  for(std::vector<HornClause*>::iterator it = hcs.hornClausesType2_1.begin();
      it != hcs.hornClausesType2_1.end(); ++it)
    os << **it << std::endl;
  std::cout << "Type 3" << std::endl;
  for(std::vector<HornClause*>::iterator it = hcs.hornClausesType3.begin();
      it != hcs.hornClausesType3.end(); ++it)
    os << **it << std::endl;
  std::cout << "Type 4" << std::endl;
  for(std::vector<HornClause*>::iterator it = hcs.hornClausesType4.begin();
      it != hcs.hornClausesType4.end(); ++it)
    os << **it << std::endl;
  return os;
}
