#include "HornClauses.h"
#define DEBUG_HORN_CLAUSES       false
#define DEBUG_ADDINGHC           false
#define DEBUG_MAKE_MATCHES       false
#define DEBUG_CE                 false
#define DEBUG_COMBINATION_HELPER false
#define DEBUG_MC2CMC2A           false
#define DEBUG_MC1CMC1A           false
#define DEBUG_MC1CMC2A           false
#define DEBUG_MC1CMC1A2          false

HornClauses::HornClauses(z3::context & ctx) : ctx(ctx){
}

HornClauses::~HornClauses(){
  for(auto it : horn_clauses)
    delete it;
}

// void HornClauses::decideHornClause(HornClause * hc, bool is_disequation){
// #if DEBUG_ADDINGHC 
//   std::cout << "Creating new horn clause " << *hc << std::endl;
// #endif
//   auxiliar_cc.transferEqClassAndPreds(original_cc);
  
//   if(!is_disequation){
//     if(hc->checkTriviality(original_cc.getEquivalenceClass())){
// #if DEBUG_ADDINGHC 
//       std::cout << "It was deleted" << std::endl;
// #endif
//       delete hc;
//       return;
//     }
//   }
// #if DEBUG_ADDINGHC 
//   std::cout << "It was added" << std::endl;
// #endif      
//   horn_clauses.push_back(hc);
//   makeMatches(hc, horn_clauses.size() - 1);
// }

// void HornClauses::mergeType2_1AndType3(HornClause * h_left, HornClause * h_right, EquationTerm & to_remove){
//   auto consequent = std::make_pair(h_right->getConsequent().first, h_right->getConsequent().second);
//   std::vector<EquationTerm> antecedent;
  
//   for(auto equation : h_left->getAntecedent())
//     antecedent.push_back(equation);
  
//   for(auto equation : h_right->getAntecedent())
//     if(!(equation.first->getId() == to_remove.first->getId())
//        || !(equation.second->getId() == to_remove.second->getId()))
//       antecedent.push_back(equation);

//   HornClause * hc = new HornClause(auxiliar_cc, antecedent, consequent);
//   combinationHelper(hc);
// }

// void HornClauses::mergeType2_1AndType4(HornClause * h1, HornClause * h2){
//   // Same as mergeType2_1AndType3
// }

// // Elimination of h_left :  * -> com_1 = uncom_1, h_right : * -> com_2 = uncom_1
// void HornClauses::mergeType2AndType2(HornClause * h_left, HornClause * h_right, Term * to_remove){
//   auto consequent = std::make_pair(h_right->getConsequent().first, h_left->getConsequent().first);
//   std::vector<EquationTerm> antecedent;

//   for(auto equation : h_left->getAntecedent())
//     antecedent.push_back(equation);
//   for(auto equation : h_right->getAntecedent())
//     antecedent.push_back(equation);

//   HornClause * hc = new HornClause(auxiliar_cc, antecedent, consequent);
//   combinationHelper(hc);
// }

// void HornClauses::mergeType2AndType3(HornClause * h_left, HornClause * h_right, Term * to_remove){
//   auto to_replace = h_left->getConsequent().first->getId() == to_remove->getId() ?
//     h_left->getConsequent().second : h_left->getConsequent().first;
//   auto consequent = std::make_pair(h_right->getConsequent().first, h_right->getConsequent().second);
//   std::vector<EquationTerm> antecedent;
  
//   for(auto equation : h_left->getAntecedent()){
//     if(equation.first->getId() == to_remove->getId())
//       antecedent.push_back(std::make_pair(equation.second, to_replace));
//     else{
//       if(equation.second->getId() == to_remove->getId())
//       antecedent.push_back(std::make_pair(equation.first, to_replace));
//       else
// 	antecedent.push_back(equation);
//     }
//   }
  
//   for(auto equation : h_right->getAntecedent()){
//     if(equation.first->getId() == to_remove->getId())
//       antecedent.push_back(std::make_pair(equation.second, to_replace));
//     else{
//       if(equation.second->getId() == to_remove->getId())
//       antecedent.push_back(std::make_pair(equation.first, to_replace));
//       else
// 	antecedent.push_back(equation);
//     }
//   }

//   HornClause * hc = new HornClause(auxiliar_cc, antecedent, consequent);
//   combinationHelper(hc);
// }

// void HornClauses::mergeType2AndType4(HornClause * h1, HornClause * h2){
//   // Same as mergeType2AndType3
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

// // -------------------------------------
// // It fills the data structures
// // Match1 mc1_antecedent, mc1_consequent
// // Match2 mc2_antecedent, mc2_consequent
// // when a new horn clause is introduced
// // -------------------------------------
// // Precondition: 
// // All HornClauses here are assumed
// // to be normalized 
// // -------------------------------------
// void HornClauses::makeMatches(HornClause * hc, unsigned current_index){
// #if DEBUG_MAKE_MATCHES
//   std::cout << "Making matches for " << *hc << std::endl;
// #endif
//   EquationTerm & hc_consequent = hc->getConsequent();

//   // -----------------------------------------------------------------------------------
//   // Processing the antedecent of the current Horn Clause
//   for(auto equation_iterator : hc->getAntecedent()) {
//     // If the first term is uncommon,
//     // then the equation is uncommon due to
//     // the normalizing ordering used
//     if(!equation_iterator.first->getSymbolCommonQ()){
// #if DEBUG_MAKE_MATCHES
//       std::cout << "It was added to mc2_antecedent" << std::endl;
// #endif
//       mc2_antecedent[std::make_pair(equation_iterator.first,
// 				    equation_iterator.second)].push_back(current_index);
//       // We also consider the mc2_antecedent as two
//       // mc1_antecedent elements
//       mc1_antecedent[equation_iterator.first].push_back(current_index);
//       mc1_antecedent[equation_iterator.second].push_back(current_index);
//     }
//     else{
//       // If the first term is common and
//       // the second term is common, then
//       // there is nothing to do!
//       if(!equation_iterator.second->getSymbolCommonQ()){
// #if DEBUG_MAKE_MATCHES
// 	std::cout << "It was added to mc1_antecedent" << std::endl;
// #endif
// 	mc1_antecedent[equation_iterator.second].push_back(current_index);
//       }
//     }
//   }
//   // -----------------------------------------------------------------------------------
  
//   // -----------------------------------------------------------------------------
//   // Processing the consequent of the current Horn Clause
//   if(!hc_consequent.first->getSymbolCommonQ()){
// #if DEBUG_MAKE_MATCHES
//     std::cout << "It was added to mc2_consequent" << std::endl;
// #endif
//     mc2_consequent[std::make_pair(hc_consequent.first,
// 				  hc_consequent.second)].push_back(current_index);
//     // We also consider the mc2_consequent as two
//     // mc1_consequent elements
//     mc1_consequent[hc_consequent.first].push_back(current_index);
//     mc1_consequent[hc_consequent.second].push_back(current_index);
//   }
//   else{
//     if(!hc_consequent.second->getSymbolCommonQ()){
// #if DEBUG_MAKE_MATCHES
//       std::cout << "It was added to mc1_consequent" << std::endl;
// #endif
//       mc1_consequent[hc_consequent.second].push_back(current_index);
//     }
//     // If the first term is common and
//     // the second term is common, then
//     // there is nothing to do
//   }
//   // -----------------------------------------------------------------------------
// }

// void HornClauses::combinationHelper(HornClause * hc){
//   auxiliar_cc.transferEqClassAndPreds(original_cc);
  
//   if(hc->checkTriviality(original_cc.getEquivalenceClass())){
// #if DEBUG_COMBINATION_HELPER
//     std::cout << "Inside combination helper: " << *hc << " was deleted" << std::endl << std::endl;
// #endif
//     delete hc;
//     return;
//   }

// // Elimination of h_left : * -> uncom_1 = uncom_2, h_right : * ^ uncom_1 = uncom_2 ^ * -> *
// void HornClauses::mc2ConsequentAndmc2Antecedent(SetOfUnsignedPairs & prev_combinations, bool & change){
//   for(auto map_equation_positions : mc2_consequent){
//     auto equation = map_equation_positions.first;
//     for(unsigned left_consequent : mc2_consequent[equation])
//       for(unsigned right_antecedent : mc2_antecedent[equation]){
// 	if(notInSet(std::make_pair(left_consequent, right_antecedent), prev_combinations)
// 	   && notInSet(std::make_pair(right_antecedent, left_consequent), prev_combinations)){
// #if DEBUG_MC2CMC2A
// 	  std::cout << "1. Combine " << left_consequent << ", "
// 		    << right_antecedent << std::endl
// 		    << *horn_clauses[left_consequent] << std::endl
// 		    << " with " << std::endl
// 		    << *horn_clauses[right_antecedent]
// 		    << std::endl;
// #endif			
// 	  prev_combinations.insert(std::make_pair(left_consequent, right_antecedent));
// 	  mergeType2_1AndType3(horn_clauses[left_consequent], horn_clauses[right_antecedent], equation);
// 	  change = true;
// 	}
//       }
//   }
// }

// // Elimination of h_left : * -> com_1 = uncom, h_right : * ^ com_2 = uncom ^ * -> *
// void HornClauses::mc1ConsequentAndmc1Antecedent(SetOfUnsignedPairs & prev_combinations, bool & change){  
//   for(auto map_vertex_positions : mc1_consequent){		
//     auto vertex = map_vertex_positions.first;
//     for(unsigned left_consequent : mc1_consequent[vertex]){
//       for(unsigned right_antecedent : mc1_antecedent[vertex]){
// 	if(notInSet(std::make_pair(left_consequent, right_antecedent), prev_combinations)
// 	   && notInSet(std::make_pair(right_antecedent, left_consequent), prev_combinations)
// 	   && horn_clauses[left_consequent]->getAntecedentCommon()){
// #if DEBUG_MC1CMC1A
// 	    std::cout << "2. Combine " << left_consequent << " , "
// 		      << right_antecedent << std::endl
// 		      << *horn_clauses[left_consequent] << std::endl
// 		      << " with " << std::endl << *horn_clauses[right_antecedent]
// 		      << std::endl;
// #endif 
// 	    prev_combinations.insert(std::make_pair(left_consequent, right_antecedent));
// 	    mergeType2AndType3(horn_clauses[left_consequent], horn_clauses[right_antecedent], vertex);
// 	    change = true;
// 	  }
//       }
//     }
//   }
// }

// // Elimination of h_left : * -> com = uncom_1, h_right : * ^ uncomm_1 = uncom_2 ^ * -> *
// void HornClauses::mc1ConsequentAndmc2Antecedent(SetOfUnsignedPairs & prev_combinations, bool & change){
//   for(auto map_vertex_positions_consequent : mc1_consequent){
//     auto vertex = map_vertex_positions_consequent.first; // (uncom_1)
//     for(unsigned left_consequent : mc1_consequent[vertex]){
//       for(auto map_equation_positions_antecedent : mc2_antecedent){
// 	auto equation_antecedent = map_equation_positions_antecedent.first;
// 	if(equation_antecedent.first == vertex || equation_antecedent.second == vertex){
// 	  for(unsigned right_antecedent : mc2_antecedent[equation_antecedent]){
// 	    if(notInSet(std::make_pair(left_consequent, right_antecedent), prev_combinations)
// 	       && notInSet(std::make_pair(right_antecedent, left_consequent), prev_combinations)
// 	       && horn_clauses[left_consequent]->getAntecedentCommon()){
// #if DEBUG_MC1CMC2A
// 	      std::cout << "3. Combine " << left_consequent << ", "
// 			<< right_antecedent << std::endl
// 			<< *horn_clauses[left_consequent] << std::endl
// 			<< " with " << std::endl
// 			<< *horn_clauses[right_antecedent]
// 			<< std::endl;
// #endif				
// 	      prev_combinations.insert(std::make_pair(left_consequent, right_antecedent));
// 	      mergeType2AndType3(horn_clauses[left_consequent], horn_clauses[right_antecedent], vertex);
// 	      change = true;
// 	    }
// 	  }
// 	}
//       }
//     }
//   }
// }

// // Elimination of h_left :  * -> com_1 = uncom_1, h_right : * -> com_2 = uncom_1
// void HornClauses::mc1ConsequentAndmc1Consequent(SetOfUnsignedPairs & prev_combinations, bool & change){
//   for(auto map_vertex_positions : mc1_consequent){
//     auto vertex = map_vertex_positions.first;
//     for(unsigned left_consequent : mc1_consequent[vertex])
//       for(unsigned right_consequent : mc1_consequent[vertex]){
//   	if(left_consequent != right_consequent
// 	   && notInSet(std::make_pair(left_consequent, right_consequent), prev_combinations)
//   	   && notInSet(std::make_pair(right_consequent, left_consequent), prev_combinations)
//   	   && horn_clauses[left_consequent]->getAntecedentCommon()
//   	   && horn_clauses[right_consequent]->getAntecedentCommon()){
// #if DEBUG_MC1CMC1A2
//   	  std::cout << "4. Combine " << left_consequent << ", "
// 		    << right_consequent << std::endl
//   		    << *horn_clauses[left_consequent] << std::endl
//   		    << " with " << std::endl << *horn_clauses[right_consequent]
//   		    << std::endl;
// #endif	    
//   	  prev_combinations.insert(std::make_pair(left_consequent, right_consequent));
//   	  mergeType2AndType2(horn_clauses[left_consequent], horn_clauses[right_consequent], vertex);
//   	  change = true;
//   	}
//       }
//   }
// }
  
// #if DEBUG_COMBINATION_HELPER
//   std::cout << "Inside combination helper: " << *hc << " was added!" << std::endl << std::endl;
// #endif
  
//   horn_clauses.push_back(hc);
//   // makeMatches is called for all the additions
//   // done by combinationHelper inside
//   // HornClauses::conditionalElimination
// }

// template<typename A>
// void HornClauses::swap(std::vector<A> & a, unsigned i, unsigned j){
//   A temp = a[i];
//   a[i] = a[j];
//   a[j] = temp;
// }

void HornClauses::add(HornClause * hc){
  
  z3::expr & consequent = hc->getConsequent();
  switch(consequent.decl().decl_kind()){
  case Z3_OP_EQ:
    if(hc->checkTriviality()){
      delete hc;
      return;
    }
    horn_clauses.push_back(hc);
    // debugging -------------------
    // std::cout << *this << std::endl;
    //           -------------------
    return;
  default:
    horn_clauses.push_back(hc);
    return;
  }
}

// void HornClauses::addHornClause(Term* u, Term* v, bool is_disequation){
//   HornClause * hc = new HornClause(auxiliar_cc, u, v, is_disequation);
//   decideHornClause(hc, is_disequation);
// }

// void HornClauses::addHornClause(std::vector<EquationTerm> & antecedent, EquationTerm & consequent, bool is_disequation){
//   HornClause * hc = new HornClause(auxiliar_cc, antecedent, consequent);
//   decideHornClause(hc, is_disequation);
// }

// void HornClauses::conditionalElimination(){
//   bool change = true;
//   SetOfUnsignedPairs prev_combinations;
//   unsigned old_horn_clauses_size, new_horn_clauses_size;
  
//   while(change){
	
//     change = false;
//     old_horn_clauses_size = horn_clauses.size();

//     // 1.
//     // This part covers cases:
//     // 1. Type 2.1 + Type 3
//     // 2. Type 2.1 + Type 4
//     // Some Type 4 + Type 3 || Type 4
//     // with mc2_consequent x mc2_antecedent
//     mc2ConsequentAndmc2Antecedent(prev_combinations, change);

//     // 2.
//     // This part covers cases:
//     // 4. Type 2 + Type 3
//     // 5. Type 2 + Type 4
//     // with mc1_consequent x mc1_antecedent
//     mc1ConsequentAndmc1Antecedent(prev_combinations, change);

//     // 3.
//     // This part covers cases:
//     // 4. Type 2 + Type 3
//     // 5. Type 2 + Type 4
//     // with mc1_consequent x mc2_antecedent
//     mc1ConsequentAndmc2Antecedent(prev_combinations, change);

//     // 4.
//     // This part covers cases:
//     // 3. Type 2 + Type 2
//     // with mc1_consequent x mc1_consequent
//     mc1ConsequentAndmc1Consequent(prev_combinations, change);

//     // Update the match data structures
//     mc1_antecedent.clear();
//     mc1_consequent.clear();
//     mc2_antecedent.clear();
//     mc2_consequent.clear();
	
//     new_horn_clauses_size = horn_clauses.size();
//     for(unsigned index = old_horn_clauses_size; index < new_horn_clauses_size; ++index)
//       makeMatches(horn_clauses[index], index);
//   }
  
//   simplifyHornClauses();
 
// #if DEBUG_CE
//   std::cout << "Horn Clauses produced - after simplify:" << std::endl;
//   for(auto it : reduced)
//     for(unsigned i = 0; i < reduced_length[it.first]; ++i)
//       std::cout << *horn_clauses[it.second[i]] << std::endl;
// #endif 
//   auxiliar_cc.transferEqClassAndPreds(original_cc);
// }

unsigned HornClauses::size(){
  return horn_clauses.size();
}

std::vector<HornClause*> & HornClauses::getHornClauses(){
  return horn_clauses;
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

// std::ostream & HornClauses::printMatch1(std::ostream & os, Match1 & m1){
//   for(auto term_it : m1){
//     os << term_it.first->to_string()
//        << std::endl;
//     for(auto position : m1[term_it.first])
//       os << position << " ";
//     os << std::endl;
//   }
//   return os;
// }

// std::ostream & HornClauses::printMatch2(std::ostream & os, Match2 & m2){
//   for(auto equation_it : m2){
//     os << equation_it.first.first->to_string()
//        << " = " << equation_it.first.second->to_string()
//        << std::endl;
//     for(auto position : m2[equation_it.first])
//       os << position << " ";
//     os << std::endl;
//   }
//   return os;
// }

std::ostream & operator << (std::ostream & os, const HornClauses & hcs){
  unsigned i = 1;
  for(auto it : hcs.horn_clauses){
    os << i << ". " << it << " " << *it << std::endl;
    ++i;
  }
  return os;
}
