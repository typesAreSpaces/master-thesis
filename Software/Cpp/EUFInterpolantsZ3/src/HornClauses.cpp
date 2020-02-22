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

HornClauses::HornClauses(z3::context & ctx, const z3::expr_vector & subterms, unsigned & min_id) :
  ctx(ctx),
  subterms(subterms), min_id(min_id){
}

HornClauses::~HornClauses(){
  for(auto it : horn_clauses)
    delete it;
}

void HornClauses::makeMatchesHelper(const z3::expr & equality,
				    unsigned current_index,
				    Match & m1, Match & m2){
  auto lhs = equality.arg(0), rhs = equality.arg(1);
  // If the first term is uncommon,
  // then the equation is uncommon due to
  // the normalizing ordering used
  if(!lhs.is_common()){
#if DEBUG_MAKE_MATCHES
    std::cout << "----------------It was added to m2" << std::endl;
#endif
    m2.push_back(equality, current_index);
    // We also consider the mc2_consequent as two
    // mc1_consequent elements
    m1.push_back(lhs, current_index);
    m1.push_back(rhs, current_index);
  }
  else{
    if(!rhs.is_common()){
#if DEBUG_MAKE_MATCHES
      std::cout << "----------------It was added to m1" << std::endl;
#endif
      m1.push_back(rhs, current_index);
    }
    // If the first term is common and
    // the second term is common, then
    // there is nothing to do
  }
}

// --------------------------------------
// This function fills the following data
// structures
// Match mc1_antecedent, mc1_consequent
// Match mc2_antecedent, mc2_consequent
// when a new horn clause is introduced
// --------------------------------------
// Precondition: 
// All HornClauses here are assumed
// to be normalized and oriented
// --------------------------------------
void HornClauses::makeMatches(HornClause * hc, unsigned current_index){
#if DEBUG_MAKE_MATCHES
  std::cout << "----Making matches for " << *hc << std::endl;
#endif
  // -----------------------------------------------------------------------------------
  // Processing the antedecent of the current Horn Clause ------------------------------
  for(auto equation_iterator : hc->getAntecedent()){
    // If the first term is uncommon,
    // then the equation is uncommon due to
    // the normalizing ordering used
#if DEBUG_MAKE_MATCHES
    std::cout << "--------Processing the antecedent" << std::endl;
#endif
    makeMatchesHelper(equation_iterator, current_index, mc1_antecedent, mc2_antecedent);
  }
  // -----------------------------------------------------------------------------------
  // -----------------------------------------------------------------------------
  // Processing the consequent of the current Horn Clause ------------------------
  auto hc_consequent = hc->getConsequent();
  auto consequent_name = hc_consequent.decl().name().str();
  if(consequent_name == "false")
    return;
#if DEBUG_MAKE_MATCHES
  std::cout << "--------Processing the consequent" << std::endl;
#endif
  makeMatchesHelper(hc_consequent, current_index, mc1_consequent, mc2_consequent);
  // -----------------------------------------------------------------------------
  return;
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

// KEEP WORKING HERE
void HornClauses::mergeType2_1AndType3(HornClause * h_left, HornClause * h_right, const z3::expr & to_remove){
  // auto consequent = std::make_pair(h_right->getConsequent().first, h_right->getConsequent().second);
  // std::vector<EquationTerm> antecedent;
  
  // for(auto equation : h_left->getAntecedent())
  //   antecedent.push_back(equation);
  
  // for(auto equation : h_right->getAntecedent())
  //   if(!(equation.first->getId() == to_remove.first->getId())
  //      || !(equation.second->getId() == to_remove.second->getId()))
  //     antecedent.push_back(equation);

  // HornClause * hc = new HornClause(auxiliar_cc, antecedent, consequent);
  // combinationHelper(hc);
}

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

// Elimination of h_left : * -> uncom_1 = uncom_2, h_right : * ^ uncom_1 = uncom_2 ^ * -> *
// i.e. conditional reduction of h_right using h_left
void HornClauses::mc2ConsequentAndmc2Antecedent(SetOfUnsignedPairs & prev_combinations, bool & change){
  unsigned _size = mc2_consequent.size();
  for(unsigned i = min_id; i < _size; i++){
    for(unsigned h_left : mc2_consequent[i]){
      for(unsigned h_right : mc2_antecedent[i]){
	
	if(notInSet(std::make_pair(h_left, h_right), prev_combinations)
	   && horn_clauses[h_left]->isCommonAntecedent()
	   && !horn_clauses[h_right]->isCommonConsequent()){
#if DEBUG_MC2CMC2A
	  std::cout << "1. Combine " << h_left << ", "
		    << h_right << std::endl
		    << *horn_clauses[h_left] << std::endl
		    << " with" << std::endl
		    << *horn_clauses[h_right] << std::endl;
#endif			
	  prev_combinations.insert(std::make_pair(h_left, h_right));
	  // mergeType2_1AndType3(horn_clauses[h_left], horn_clauses[h_right], subterms[i]);
	  change = true;
	}
      }
    }
  }
}

// Elimination of h_left : * -> com_1 = uncom, h_right : * ^ com_2 = uncom ^ * -> *
// i.e. conditional reduction of h_right using h_left
void HornClauses::mc1ConsequentAndmc1Antecedent(SetOfUnsignedPairs & prev_combinations, bool & change){
  unsigned _size = mc1_consequent.size();
  for(unsigned i = min_id; i < _size; i++){
    for(unsigned h_left : mc1_consequent[i]){
      for(unsigned h_right : mc1_antecedent[i]){
	
	if(notInSet(std::make_pair(h_left, h_right), prev_combinations)
	   && horn_clauses[h_left]->isCommonAntecedent()
	   && !horn_clauses[h_right]->isCommonConsequent()){
#if DEBUG_MC1CMC1A
	  std::cout << "2. Combine " << h_left << ", "
		    << h_right << std::endl
		    << *horn_clauses[h_left] << std::endl
		    << " with" << std::endl
		    << *horn_clauses[h_right] << std::endl;
#endif 
	  prev_combinations.insert(std::make_pair(h_left, h_right));
	  // mergeType2AndType3(horn_clauses[h_left], horn_clauses[h_right], vertex);
	  // change = true;
	}
      }
    }
  }
}

// Elimination of h_left : * -> com = uncom_1, h_right : * ^ uncomm_1 = uncom_2 ^ * -> *
// i.e. conditional reduction of h_right using h_left
void HornClauses::mc1ConsequentAndmc2Antecedent(SetOfUnsignedPairs & prev_combinations, bool & change){
  unsigned _size_mc1_consequent = mc1_consequent.size(), _size_mc2_antecedent = mc2_antecedent.size();
  for(unsigned i = min_id; i < _size_mc1_consequent; i++){
    for(auto h_left : mc1_consequent[i]){
      for(unsigned j = min_id; j < _size_mc2_antecedent; j++){
	if(mc2_antecedent[j].size() > 0){
	  auto equation_right = subterms[j];
	  if(equation_right.arg(0).id() == i || equation_right.arg(1).id() == i){
	    for(auto h_right : mc2_antecedent[j]){
	      
	      if(notInSet(std::make_pair(h_left, h_right), prev_combinations)
		 && horn_clauses[h_left]->isCommonAntecedent()
		 && !horn_clauses[h_right]->isCommonConsequent()){
#if DEBUG_MC1CMC2A
		std::cout << "3. Combine " << h_left << ", "
			  << h_right << std::endl
			  << *horn_clauses[h_left] << std::endl
			  << " with" << std::endl
			  << *horn_clauses[h_right] << std::endl;
#endif				
		prev_combinations.insert(std::make_pair(h_left, h_right));
		// mergeType2AndType3(horn_clauses[h_left], horn_clauses[h_right], vertex);
		// change = true;
	      }	    
	    }
	  }
	}
      }
    }
  }
}

// Elimination of h_left :  * -> com_1 = uncom_1, h_right : * -> com_2 = uncom_1
// i.e. conditional reduction of h_right using h_left
void HornClauses::mc1ConsequentAndmc1Consequent(SetOfUnsignedPairs & prev_combinations, bool & change){
  unsigned _size = mc1_consequent.size();
  for(unsigned i = min_id; i < _size; i++){
    for(auto h_left : mc1_consequent[i]){
      for(auto h_right : mc1_consequent[i]){
	
	if(h_left != h_right
	   && notInSet(std::make_pair(h_left, h_right), prev_combinations)
  	   && horn_clauses[h_left]->isCommonAntecedent()
  	   && !horn_clauses[h_right]->isCommonConsequent()){ // Be careful with this condition
#if DEBUG_MC1CMC1A2
  	  std::cout << "4. Combine " << h_left << ", "
		    << h_right << std::endl
  		    << *horn_clauses[h_left] << std::endl
  		    << " with" << std::endl
		    << *horn_clauses[h_right] << std::endl;
#endif	    
  	  prev_combinations.insert(std::make_pair(h_left, h_right));
  	  // mergeType2AndType2(horn_clauses[h_left], horn_clauses[h_right], vertex);
  	  // change = true;
	}
      }
    }
  }
}

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
    curr_num_horn_clauses++;
    makeMatches(hc, curr_num_horn_clauses - 1);
    return;
  default:
    horn_clauses.push_back(hc);
    curr_num_horn_clauses++;
    makeMatches(hc, curr_num_horn_clauses - 1); 
    return;
  }
}

void HornClauses::conditionalElimination(){
  bool change = true;
  SetOfUnsignedPairs prev_combinations;
  unsigned old_size, new_size;
  
  while(change){
	
    change = false;
    old_size = horn_clauses.size();

    // 1.
    // This part covers cases:
    // 1. Type 2.1 + Type 3
    // 2. Type 2.1 + Type 4
    // Some Type 4 + Type 3 || Type 4
    // with mc2_consequent x mc2_antecedent
    mc2ConsequentAndmc2Antecedent(prev_combinations, change);

    // 2.
    // This part covers cases:
    // 4. Type 2 + Type 3
    // 5. Type 2 + Type 4
    // with mc1_consequent x mc1_antecedent
    mc1ConsequentAndmc1Antecedent(prev_combinations, change);

    // 3.
    // This part covers cases:
    // 4. Type 2 + Type 3
    // 5. Type 2 + Type 4
    // with mc1_consequent x mc2_antecedent
    mc1ConsequentAndmc2Antecedent(prev_combinations, change);

    // 4.
    // This part covers cases:
    // 3. Type 2 + Type 2
    // with mc1_consequent x mc1_consequent
    mc1ConsequentAndmc1Consequent(prev_combinations, change);

    // Update the match data structures
    // mc1_antecedent.clear();
    // mc1_consequent.clear();
    // mc2_antecedent.clear();
    // mc2_consequent.clear();
	
    new_size = horn_clauses.size();
    for(unsigned i = old_size; i < new_size; i++)
      makeMatches(horn_clauses[i], i);
  }
  
  // simplifyHornClauses();
 
// #if DEBUG_CE
//   std::cout << "Horn Clauses produced - after simplify:" << std::endl;
//   for(auto it : reduced)
//     for(unsigned i = 0; i < reduced_length[it.first]; ++i)
//       std::cout << *horn_clauses[it.second[i]] << std::endl;
// #endif 
}

unsigned HornClauses::size(){
  return horn_clauses.size();
}

std::vector<HornClause*> & HornClauses::getHornClauses(){
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
  
  return os;
}
