#include "HornClauses.h"

unsigned HornClauses::numHornClauses = 0;

HornClauses::HornClauses(){
}

HornClauses::~HornClauses(){
  for(std::vector<HornClause*>::iterator it = hornClauses.begin();
      it != hornClauses.end(); ++it){
    delete *it;
  }
}

void HornClauses::addHornClause(UnionFind & uf, Vertex* u, Vertex* v, std::vector<Vertex*> & terms){
  HornClause * hc = new HornClause(uf, u, v, terms);
  hc->normalize();
  if(hc->checkTrivial())
    delete hc;
  hornClauses.push_back(hc);
  ++numHornClauses;
}

void HornClauses::conditionalElimination(){
  //TODO: Finish this method
  std::cout << numHornClauses << std::endl;
  
}

std::ostream & operator << (std::ostream & os, HornClauses & hcs){
  for(std::vector<HornClause*>::iterator it = hcs.hornClauses.begin();
      it != hcs.hornClauses.end(); ++it){
    os << **it << std::endl;
  }
  return os;
}
