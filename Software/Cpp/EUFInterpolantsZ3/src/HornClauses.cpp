#include "HornClauses.h"
#define DEBUG_HORN_CLAUSES       false
#define DEBUG_ADDINGHC           false
#define DEBUG_MAKE_MATCHES       false
#define DEBUG_CE                 false
#define DEBUG_COMBINATION_HELPER false
#define DEBUG_MATCHES            false
#define DEBUG_DESTRUCTOR_HCS     false

HornClauses::HornClauses(UnionFindExplain & ufe) : ufe(ufe) {}

HornClauses::~HornClauses(){
  for(auto it : horn_clauses)
    delete it;
#if DEBUG_DESTRUCTOR_HCS
  std::cout << "Done ~HornClauses" << std::endl;
#endif
}

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
    if(hc->checkTriviality(ufe)){
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
  std::cout << "HornClauses::conditionalElimination not implemented yet!" << std::endl;
  
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
  os << "Horn clauses produced" << std::endl;
  for(auto it : hcs.horn_clauses){
    os << i << ". " << it << " " << *it << std::endl;
    ++i;
  }
  os << "Number of horn clauses: " << i;

  return os;
}
