#include "HornClauses.h"
#define DEBUG_HORN_CLAUSES       false
#define DEBUG_ADDINGHC           false
#define DEBUG_MAKE_MATCHES       false
#define DEBUG_CE                 false
#define DEBUG_COMBINATION_HELPER false
#define DEBUG_MC2CMC2A           true
#define DEBUG_MC1CMC1A           true
#define DEBUG_MC1CMC2A           true
#define DEBUG_MC1CMC1A2          true
#define DEBUG_MATCHES            false
#define DEBUG_DESTRUCTOR_HCS     true

HornClauses::HornClauses(z3::context & ctx, const z3::expr_vector & subterms, const unsigned & min_id) :
  ctx(ctx),
  subterms(subterms), min_id(min_id){
}

HornClauses::~HornClauses(){
  for(auto it : horn_clauses)
    delete it;
#if DEBUG_DESTRUCTOR_HCS
  std::cout << "Done ~HornClauses" << std::endl;
#endif
}

// void HornClauses::combinationHelper(HornClause * hc){
//   auxiliar_cc.transferEqClassAndPreds(original_cc);
  
//   if(hc->checkTriviality(original_cc.getEquivalenceClass())){
// #if DEBUG_COMBINATION_HELPER
//     std::cout << "Inside combination helper: " << *hc << " was deleted" << std::endl << std::endl;
// #endif
//     delete hc;
//     return;
//   }
// #if DEBUG_COMBINATION_HELPER
//   std::cout << "Inside combination helper: " << *hc << " was added!" << std::endl << std::endl;
// #endif
  
//   horn_clauses.push_back(hc);
//   // makeMatches is called for all the additions
//   // done by combinationHelper inside
//   // HornClauses::conditionalElimination
// }

// // This method removes unnecessary
// // extra Horn Clauses
// // Implements the following rule:
// // C, D -> a     C -> a
// // ---------------------
// //       C -> a
// void HornClauses::simplifyHornClauses(){
//   unsigned position = 0;
//   bool change = true;
  
//   // Filter: Only Type 2 or Type 2.1 are allowed here		
//   for(auto it : horn_clauses){	
//     if(it->getAntecedentCommon()
//        && it->getConsequent().first->getSymbolCommonQ()){
//       reduced[it->getConsequent()].push_back(position);
//     }
//     ++position;
//   }
  
//   for(auto horn_clause : reduced){
//     unsigned num_of_positions = horn_clause.second.size();
//     for(unsigned i = 0; i + 1 < num_of_positions; ++i){
//       unsigned j = i + 1;
//       while(change && j < num_of_positions){
// 	change = false;
// 	unsigned i_position = horn_clause.second[i],
// 	  j_position = horn_clause.second[j],
// 	  last_position = horn_clause.second[num_of_positions - 1];
	
// 	if(*horn_clauses[i_position] > *horn_clauses[j_position]){
// 	  change = true;
// 	  swap(horn_clauses, j_position, last_position);
// 	  --num_of_positions;
// 	}
// 	else{
// 	  if(*horn_clauses[i_position] < *horn_clauses[j_position]){
// 	    change = true;
// 	    swap(horn_clauses, i_position, j_position);
// 	    swap(horn_clauses, j_position, last_position);
// 	    --num_of_positions;
// 	  }
// 	  else
// 	    ++j; 
// 	}
//       }
//     }
//     reduced_length[horn_clause.first] = num_of_positions;
//   }
// }

// template<typename A>
// void HornClauses::swap(std::vector<A> & a, unsigned i, unsigned j){
//   A temp = a[i];
//   a[i] = a[j];
//   a[j] = temp;
// }

void HornClauses::add(HornClause * hc){
  const z3::expr & consequent = hc->getConsequent();
  switch(consequent.decl().decl_kind()){
  case Z3_OP_EQ:
    if(hc->checkTriviality()){
      delete hc;
      return;
    }
    horn_clauses.push_back(hc);
    curr_num_horn_clauses++;
    return;
  default: // The contradiction/false-value
    horn_clauses.push_back(hc);
    curr_num_horn_clauses++;
    return;
  }
}

void HornClauses::conditionalElimination(std::vector<Replacement> replacements){
  std::cout << "ok1" << std::endl;
  
  // simplifyHornClauses();
 
// #if DEBUG_CE
//   std::cout << "Horn Clauses produced - after simplify:" << std::endl;
//   for(auto it : reduced)
//     for(unsigned i = 0; i < reduced_length[it.first]; ++i)
//       std::cout << *horn_clauses[it.second[i]] << std::endl;
// #endif 
}

unsigned HornClauses::size() const {
  return horn_clauses.size();
}

unsigned HornClauses::maxID() const {
  return subterms.size();
}

const std::vector<HornClause*> & HornClauses::getHornClauses() const {
  return horn_clauses;
}

HornClause* HornClauses::operator[](unsigned i){
  return horn_clauses[i];
}

// std::vector<HornClause*> HornClauses::getHornClauses(){
//   std::vector<HornClause*> new_hcs;
//   for(auto it : horn_clauses){
//     auto consequent = it->getConsequent();
//     if(it->getAntecedentCommon()
//        && consequent.first->getSymbolCommonQ()
//        && consequent.second->getSymbolCommonQ())
//       new_hcs.push_back(it);
//   }
//   return new_hcs;
// }

// std::vector<HornClause*> HornClauses::getReducibleHornClauses(){
//   std::vector<HornClause*> new_hcs;
//   for(auto it : reduced)
//     for(unsigned index = 0; index < reduced_length[it.first]; ++index)
//       new_hcs.push_back(horn_clauses[it.second[index]]);
//   return new_hcs;
// }

std::ostream & operator << (std::ostream & os, const HornClauses & hcs){
  unsigned i = 0;
  std::cout << "Horn clauses produced" << std::endl;
  for(auto it : hcs.horn_clauses){
    os << i << ". " << it << " " << *it << std::endl;
    ++i;
  }

#if DEBUG_MATCHES
  os << "mc1_antecedent"   << std::endl;
  Match::iterator it = hcs.mc1_antecedent.begin(), end = hcs.mc1_antecedent.end();
  i = 0;
  for(; it != end; ++it){
    if((*it).size() > 0){
      os << "Term : " << hcs.subterms[i] << std::endl;
      os << "Horn Clauses:" << std::endl;
      for(auto position : *it)
      	os << *hcs.horn_clauses[position] << std::endl;
    }
    i++;
  }
  
  os << "mc1_consequent"   << std::endl;
  it = hcs.mc1_consequent.begin(), end = hcs.mc1_consequent.end();
  i = 0;
  for(; it != end; ++it){
    if((*it).size() > 0){
      os << "Term : " << hcs.subterms[i] << std::endl;
      os << "Horn Clauses:" << std::endl;
      for(auto position : *it)
      	os << *hcs.horn_clauses[position] << std::endl;
    }
    i++;
  }
  
  os << "mc2_antecedent"   << std::endl;
  it = hcs.mc2_antecedent.begin(), end = hcs.mc2_antecedent.end();
  i = 0;
  for(; it != end; ++it){
    if((*it).size() > 0){
      os << "Term : " << hcs.subterms[i] << std::endl;
      os << "Horn Clauses:" << std::endl;
      for(auto position : *it)
      	os << *hcs.horn_clauses[position] << std::endl;
    }
    i++;
  }
  
  os << "mc2_consequent"   << std::endl;
  it = hcs.mc2_consequent.begin(), end = hcs.mc2_consequent.end();
  i = 0;
  for(; it != end; ++it){
    if((*it).size() > 0){
      os << "Term : " << hcs.subterms[i] << std::endl;
      os << "Horn Clauses:" << std::endl;
      for(auto position : *it)
      	os << *hcs.horn_clauses[position] << std::endl;
    }
    i++;
  }
#endif  
  return os;
}
