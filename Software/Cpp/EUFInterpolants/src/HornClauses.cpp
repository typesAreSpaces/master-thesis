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
    if(hc->getConsequentQ()){
      hornClausesType1.push_back(hc);
    }
    else{
      if(!hc->getMaximalConsequentQ()){
	hornClausesType2_1.push_back(hc);
      }
      else{
	hornClausesType2.push_back(hc);
      }
    }
  }
  else{
    if(hc->getConsequentQ()){
      hornClausesType3.push_back(hc);
    }
    else{
      hornClausesType4.push_back(hc);
    }
  }

  makeMatches(hc, numHornClauses);
  ++numHornClauses;
}

void HornClauses::conditionalElimination(){

  // // Let's just print all the matches data
  // // structures to check consistency
  // // typedef std::map<Vertex*, std::vector<unsigned> > match1;
  // std::cout << "mc1A-------------------------------------" << std::endl;
  // for(match1::iterator it = mc1A.begin(); it != mc1A.end(); ++it){
  //   std::cout << it->first->to_string() << std::endl;
  //   for(std::vector<unsigned>::iterator it2 = it->second.begin();
  //       it2 != it->second.end(); ++it2)
  //     std::cout << *it2 << " ";
  //   std::cout << std::endl;
  // }
  // std::cout << "mc1A-------------------------------------" << std::endl;
  // std::cout << "mc1C-------------------------------------" << std::endl;
  // for(match1::iterator it = mc1C.begin(); it != mc1C.end(); ++it){
  //   std::cout << it->first->to_string() << std::endl;
  //   for(std::vector<unsigned>::iterator it2 = it->second.begin();
  //       it2 != it->second.end(); ++it2)
  //     std::cout << *it2 << " ";
  //   std::cout << std::endl;
  // }
  // std::cout << "mc1C-------------------------------------" << std::endl;
  // std::cout << "mc2A-------------------------------------" << std::endl;
  // for(match2::iterator it = mc2A.begin(); it != mc2A.end(); ++it){
  //   std::cout << it->first.first->to_string() << ", " << it->first.second->to_string() << std::endl;
  //   for(std::vector<unsigned>::iterator it2 = it->second.begin();
  //       it2 != it->second.end(); ++it2)
  //     std::cout << *it2 << " ";
  //   std::cout << std::endl;
  // }
  // std::cout << "mc2A-------------------------------------" << std::endl;
  // std::cout << "mc2C-------------------------------------" << std::endl;
  // for(match2::iterator it = mc2C.begin(); it != mc2C.end(); ++it){
  //   std::cout << it->first.first->to_string() << ", " << it->first.second->to_string() << std::endl;
  //   for(std::vector<unsigned>::iterator it2 = it->second.begin();
  //       it2 != it->second.end(); ++it2)
  //     std::cout << *it2 << " ";
  //   std::cout << std::endl;
  // }
  // std::cout << "mc2C-------------------------------------" << std::endl;

  bool change = true;
  std::set<std::pair<unsigned, unsigned> > prevCombinations;
  while(change){
    change = false;
    
  }
}

// Precondition: 
// All HornClauses here are assumed to be normalized
void HornClauses::makeMatches(HornClause * hc, unsigned i){
  std::vector<equality> & _antecedent = hc->getAntecedent();
  equality & _consequent = hc->getConsequent();
  for(std::vector<equality>::iterator it = _antecedent.begin();
      it != _antecedent.end(); ++it){
    // If the first term is uncommon,
    // then the equality is uncommon due to
    // the normalizing ordering used
    if(!it->first->getSymbolCommonQ())
      mc2A[std::make_pair(it->first, it->second)].push_back(i);
    else{
      // If the first term is common and
      // the second term is common, then
      // there is nothing to do!
      if(!it->second->getSymbolCommonQ())
	mc1A[it->second].push_back(i);
    }
  }
  if(!_consequent.first->getSymbolCommonQ())
    mc2C[std::make_pair(_consequent.first, _consequent.second)].push_back(i);
  else{
    // If the first term is common and
    // the second term is common, then
    // there is nothing to do!
    if(!_consequent.second->getSymbolCommonQ())
      mc1C[_consequent.second].push_back(i);
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
