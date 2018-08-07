#include "HornClauses.h"

unsigned HornClauses::numHornClauses = 0;

HornClauses::HornClauses(std::vector<Vertex*> & terms) : localTerms(terms) {
}

HornClauses::~HornClauses(){
  for(std::vector<HornClause*>::iterator it = hornClauses.begin();
      it != hornClauses.end(); ++it)
    delete *it;
}

void HornClauses::addHornClause(UnionFind & uf,
				Vertex* u, Vertex* v){
  HornClause * hc = new HornClause(uf, u, v, localTerms);
  hc->normalize();
  if(hc->checkTrivial()){
    delete hc;
    return;
  }
  hornClauses.push_back(hc);
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

    for(match2::iterator it = mc2C.begin();
	it != mc2C.end(); ++it)
      for(std::vector<unsigned>::iterator it2 = it->second.begin();
	  it2 != it->second.end(); ++it2)
	for(std::vector<unsigned>::iterator it3 = mc2A[it->first].begin();
	    it3 != mc2A[it->first].end(); ++it3){
	  if(prevCombinations.find(std::make_pair(*it2, *it3)) == prevCombinations.end()){
	    std::cout << "Combine " << *hornClauses[*it2]
		      << " with " << *hornClauses[*it3]
		      << std::endl;
	    prevCombinations.insert(std::make_pair(*it2, *it3));
	    change = true;
	  }
	}
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
      mc2A[std::make_pair(it->first,
			  it->second)].push_back(i);
    else{
      // If the first term is common and
      // the second term is common, then
      // there is nothing to do!
      if(!it->second->getSymbolCommonQ())
	mc1A[it->second].push_back(i);
    }
  }
  if(!_consequent.first->getSymbolCommonQ())
    mc2C[std::make_pair(_consequent.first,
			_consequent.second)].push_back(i);
  else{
    // If the first term is common and
    // the second term is common, then
    // there is nothing to do!
    if(!_consequent.second->getSymbolCommonQ())
      mc1C[_consequent.second].push_back(i);
  }
}

void HornClauses::mergeType2_1AndType3(HornClause * h1, HornClause * h2){
  
}
void HornClauses::mergeType2_1AndType4(HornClause * h1, HornClause * h2){
  
}
void HornClauses::mergeType2AndType2(HornClause * h1, HornClause * h2){
  
}
void HornClauses::mergeType2AndType3(HornClause * h1, HornClause * h2){
  
}
void HornClauses::mergeType2AndType4(HornClause * h1, HornClause * h2){
  
}

std::ostream & operator << (std::ostream & os, HornClauses & hcs){
  for(std::vector<HornClause*>::iterator it = hcs.hornClauses.begin();
      it != hcs.hornClauses.end(); ++it)
    os << **it << std::endl;
  return os;
}
