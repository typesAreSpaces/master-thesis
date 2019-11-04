#include "HornClauses.h"
#define DEBUG_HORN_CLAUSES       false
#define DEBUG_ADDINGHC           false
#define DEBUG_MAKE_MATCHES       false
#define DEBUG_CE                 false
#define DEBUG_COMBINATION_HELPER true
#define DEBUG_MC2CMC2A           true
#define DEBUG_MC1CMC1A           true
#define DEBUG_MC1CMC2A           false
#define DEBUG_MC1CMC1A2          false

HornClauses::HornClauses(CongruenceClosure & original_closure,
			 CongruenceClosure & auxiliar_closure) :
  original_cc(original_closure), auxiliar_cc(auxiliar_closure)
{
}

HornClauses::~HornClauses(){
  for(auto it : horn_clauses)
    delete it;
}

void HornClauses::addHornClause(Term* u, Term* v,
				bool is_disequation){
  HornClause * hc = new HornClause(auxiliar_cc, u, v, is_disequation);
  decideHornClause(hc, is_disequation);
}

void HornClauses::addHornClause(std::vector<EquationTerm> & antecedent,
				EquationTerm & consequent,
				bool is_disequation){
  HornClause * hc = new HornClause(auxiliar_cc, antecedent, consequent);
  decideHornClause(hc, is_disequation);
}

void HornClauses::decideHornClause(HornClause * hc, bool is_disequation){
#if DEBUG_ADDINGHC 
  std::cout << "Creating new horn clause " << *hc << std::endl;
#endif
  auxiliar_cc.transferEqClassAndPreds(original_cc);
  
  if(!is_disequation){
    if(hc->checkTriviality(original_cc.getEquivalenceClass())){
#if DEBUG_ADDINGHC 
      std::cout << "It was deleted" << std::endl;
#endif
      delete hc;
      return;
    }
  }
#if DEBUG_ADDINGHC 
  std::cout << "It was added" << std::endl;
#endif      
  horn_clauses.push_back(hc);
  makeMatches(hc, horn_clauses.size() - 1);
}

void HornClauses::conditionalElimination(){
  bool change = true;
  SetOfUnsignedPairs prev_combinations;
  unsigned old_horn_clauses_size, new_horn_clauses_size;
  
  while(change){
	
    change = false;
    old_horn_clauses_size = horn_clauses.size();

    // 1.
    // This part covers cases:
    // 1. Type 2.1 + Type 3
    // 2. Type 2.1 + Type 4
    // Some Type 4 + Type 3 || Type 4
    // with mc2_consequent x mc2_antecedent
    mc2ConsequentAndmc2Antecedent(prev_combinations, change); // TODO: Working on this one

    // 2.
    // This part covers cases:
    // 4. Type 2 + Type 3
    // 5. Type 2 + Type 4
    // with mc1_consequent x mc1_antecedent
    mc1ConsequentAndmc1Antecedent(prev_combinations, change); // TODO: and this one

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
    mc1ConsequentAndmc1Antecedent2(prev_combinations, change);

    // Update the match data structures
    mc1_antecedent.clear();
    mc1_consequent.clear();
    mc2_antecedent.clear();
    mc2_consequent.clear();
	
    new_horn_clauses_size = horn_clauses.size();
    for(unsigned index = old_horn_clauses_size; index < new_horn_clauses_size; ++index)
      makeMatches(horn_clauses[index], index);

  }
  
  simplifyHornClauses();
 
#if DEBUG_CE
  std::cout << "Horn Clauses produced - after simplify:" << std::endl;
  for(auto it : reduced)
    for(unsigned i = 0; i < reduced_length[it.first]; ++i)
      std::cout << *horn_clauses[it.second[i]] << std::endl;
#endif 
  auxiliar_cc.transferEqClassAndPreds(original_cc);
}

void HornClauses::mc2ConsequentAndmc2Antecedent(SetOfUnsignedPairs & prev_combinations,
						bool & change){
  for(auto map_equation_positions : mc2_consequent){
    auto equation = map_equation_positions.first;
    auto positions_consequent = map_equation_positions.second;
    for(unsigned position_consequent : positions_consequent)
      for(unsigned position_antecedent : mc2_antecedent[equation]){
	if(notInSet(std::make_pair(position_consequent,
				   position_antecedent), prev_combinations)
	   && notInSet(std::make_pair(position_antecedent,
				      position_consequent), prev_combinations)){
#if DEBUG_MC2CMC2A
	  std::cout << "1. Combine" << std::endl
		    << *horn_clauses[position_consequent] << std::endl
		    << " with " << std::endl
		    << *horn_clauses[position_antecedent]
		    << std::endl;
#endif			
	  prev_combinations.insert(std::make_pair(position_consequent,
						  position_antecedent));
	  mergeType2_1AndType3(horn_clauses[position_consequent],
			       horn_clauses[position_antecedent]);
	  change = true;
	}
      }
  }
}

void HornClauses::mc1ConsequentAndmc1Antecedent(SetOfUnsignedPairs & prev_combinations,
						bool & change){
  // unsigned i = 0;
  // for(auto x : horn_clauses){
  //   std::cout << i++ << ". " << *x << std::endl;
  //   std::cout << x->getAntecedentCommon() << std::endl;
  //   std::cout << x->getConsequentCommon() << std::endl;
  // }
  
  for(auto map_vertex_positions : mc1_consequent){		
    auto vertex = map_vertex_positions.first;
    auto positions_consequent = map_vertex_positions.second;
    for(unsigned position_consequent : positions_consequent){
      for(unsigned position_antecedent : mc1_antecedent[vertex]){
	if(notInSet(std::make_pair(position_consequent, position_antecedent), prev_combinations)
	   && notInSet(std::make_pair(position_antecedent, position_consequent), prev_combinations)
	   && horn_clauses[position_consequent]->getAntecedentCommon()){
#if DEBUG_MC1CMC1A
	    std::cout << "2. Combine " << position_consequent << " , "
		      << position_antecedent << std::endl
		      << *horn_clauses[position_consequent] << std::endl
		      << " with " << std::endl << *horn_clauses[position_antecedent]
		      << std::endl;
#endif 
	    prev_combinations.insert(std::make_pair(position_consequent, position_antecedent));
	    mergeType2AndType3(horn_clauses[position_consequent], horn_clauses[position_antecedent], vertex);
	    change = true;
	  }
      }
    }
  }
}

void HornClauses::mc1ConsequentAndmc2Antecedent(SetOfUnsignedPairs & prev_combinations,
						bool & change){
//   for(auto map_vertex_positions_consequent : mc1_consequent){
		
//     auto vertex_consequent = map_vertex_positions_consequent.first;
//     auto positions_consequent = map_vertex_positions_consequent.second;
    
//     for(unsigned position_consequent :positions_consequent){			
//       for(auto map_equation_positions_antecedent : mc2_antecedent){
// 	auto equation_antecedent = map_equation_positions_antecedent.first;
// 	auto positions_antecedent = map_equation_positions_antecedent.second;
// 	if(equation_antecedent.first == vertex_consequent ||
// 	   equation_antecedent.second == vertex_consequent)
// 	  for(unsigned position_antecedent : mc2_antecedent[equation_antecedent]){
// 	    if(notInSet(std::make_pair(position_consequent,
// 				    position_antecedent), prev_combinations)
// 	       && notInSet(std::make_pair(position_antecedent,
// 				       position_consequent), prev_combinations)
// 	       && horn_clauses[position_consequent]->getAntecedentCommon()){
// #if DEBUG_MC1CMC2A
// 	      std::cout << "3. Combine " << std::endl
// 			<< *horn_clauses[position_consequent] << std::endl
// 			<< " with " << std::endl
// 			<< *horn_clauses[position_antecedent]
// 			<< std::endl;
// #endif
				
// 	      prev_combinations.insert(std::make_pair(position_consequent,
// 						      position_antecedent));
// 	      mergeType2AndType3(horn_clauses[position_consequent],
// 				 horn_clauses[position_antecedent]);
// 	      change = true;
// 	    }
// 	  }
//       }
//     }
//   }
}

void HornClauses::mc1ConsequentAndmc1Antecedent2(SetOfUnsignedPairs & prev_combinations,
						 bool & change){
//   for(auto map_vertex_positions : mc1_consequent){
		
//     auto vertex_consequent_1 = map_vertex_positions.first;
//     auto positions_consequent_1 = map_vertex_positions.second;
//     for(unsigned position_consequent_1 : positions_consequent_1)
			
//       for(unsigned position_consequent_2 : mc1_consequent[vertex_consequent_1]){
// 	if(notInSet(std::make_pair(position_consequent_1,
// 				position_consequent_2), prev_combinations)
// 	   && notInSet(std::make_pair(position_consequent_2,
// 				   position_consequent_1), prev_combinations)
// 	   && horn_clauses[position_consequent_1]->getAntecedentCommon()
// 	   && horn_clauses[position_consequent_2]->getAntecedentCommon()){
// #if DEBUG_MC1CMC1A2
// 	  std::cout << "4. Combine " << std::endl
// 		    << *horn_clauses[position_consequent_1] << std::endl
// 		    << " with " << std::endl << *horn_clauses[position_consequent_2]
// 		    << std::endl;
// #endif	    
// 	  prev_combinations.insert(std::make_pair(position_consequent_1,
// 						  position_consequent_2));
// 	  mergeType2AndType2(horn_clauses[position_consequent_1],
// 			     horn_clauses[position_consequent_2]);
// 	  change = true;
// 	}
//       }
//   }
}

// This method removes unnecessary
// extra Horn Clauses
// Implements the following rule:
// C, D -> a     C -> a
// ---------------------
//       C -> a
void HornClauses::simplifyHornClauses(){
  unsigned position = 0;
  bool change = true;
  
  // Filter: Only Type 2 or Type 2.1 are allowed here		
  for(auto it : horn_clauses){	
    if(it->getAntecedentCommon()
       && it->getConsequent().first->getSymbolCommonQ()){
      reduced[it->getConsequent()].push_back(position);
    }
    ++position;
  }
  
  for(auto it : reduced){
    unsigned length = it.second.size();
    for(unsigned i = 0; i + 1 < length; ++i){
      unsigned j = i + 1;
      while(change && j < length){
	change = false;
	unsigned i_position = it.second[i],
	  j_position = it.second[j],
	  l_position = it.second[length - 1];
	
	if(*horn_clauses[i_position] > *horn_clauses[j_position]){
	  change = true;
	  swap(horn_clauses, j_position, l_position);
	  --length;
	}
	else{
	  if(*horn_clauses[i_position] < *horn_clauses[j_position]){
	    change = true;
	    swap(horn_clauses, i_position, j_position);
	    swap(horn_clauses, j_position, l_position);
	    --length;
	  }
	  else
	    ++j; 
	}
      }
    }
    reduced_length[it.first] = length;
  }
}


// -------------------------------------
// It fills the data structures
// Match1 mc1_antecedent, mc1_consequent
// Match2 mc2_antecedent, mc2_consequent
// when a new horn clause is introduced
// -------------------------------------
// Precondition: 
// All HornClauses here are assumed
// to be normalized 
// -------------------------------------
void HornClauses::makeMatches(HornClause * hc,
			      unsigned current_index){
#if DEBUG_MAKE_MATCHES
  std::cout << "Making matches for " << *hc << std::endl;
#endif
  
  std::vector<EquationTerm> & hc_antecedent = hc->getAntecedent();
  EquationTerm & hc_consequent = hc->getConsequent();

  // -----------------------------------------------------------------------------------
  // Processing the antedecent of the current Horn Clause
  for(auto equation_iterator : hc_antecedent) {
    // If the first term is uncommon,
    // then the equation is uncommon due to
    // the normalizing ordering used
    if(!equation_iterator.first->getSymbolCommonQ()){
#if DEBUG_MAKE_MATCHES
      std::cout << "It was added to mc2_antecedent" << std::endl;
#endif
      mc2_antecedent[std::make_pair(equation_iterator.first,
				    equation_iterator.second)].push_back(current_index);
      // We also consider the mc2_antecedent as two
      // mc1_antecedent elements
      mc1_antecedent[equation_iterator.first].push_back(current_index);
      mc1_antecedent[equation_iterator.second].push_back(current_index);
    }
    else{
      // If the first term is common and
      // the second term is common, then
      // there is nothing to do!
      if(!equation_iterator.second->getSymbolCommonQ()){
#if DEBUG_MAKE_MATCHES
	std::cout << "It was added to mc1_antecedent" << std::endl;
#endif
	mc1_antecedent[equation_iterator.second].push_back(current_index);
      }
    }
  }
  // -----------------------------------------------------------------------------------
  
  // -----------------------------------------------------------------------------
  // Processing the consequent of the current Horn Clause
  if(!hc_consequent.first->getSymbolCommonQ()){
#if DEBUG_MAKE_MATCHES
    std::cout << "It was added to mc2_consequent" << std::endl;
#endif
    mc2_consequent[std::make_pair(hc_consequent.first,
				  hc_consequent.second)].push_back(current_index);
    // We also consider the mc2_consequent as two
    // mc1_consequent elements
    mc1_consequent[hc_consequent.first].push_back(current_index);
    mc1_consequent[hc_consequent.second].push_back(current_index);
  }
  else{
    if(!hc_consequent.second->getSymbolCommonQ()){
#if DEBUG_MAKE_MATCHES
      std::cout << "It was added to mc1_consequent" << std::endl;
#endif
      mc1_consequent[hc_consequent.second].push_back(current_index);
    }
    // If the first term is common and
    // the second term is common, then
    // there is nothing to do
  }
  // -----------------------------------------------------------------------------
  
}

void HornClauses::mergeType2_1AndType3(HornClause * h1, HornClause * h2){

  // UnionFind _h1LocalUf = h1->getLocalUF(),
  //   _h2LocalUf = HornClause::getGlobalUF();

  // std::vector<EquationTerm> _h1Antecedent = h1->getAntecedent(),
  //   _h2Antecedent = h2->getAntecedent();
  // EquationTerm _h1Consequent = h1->getConsequent(),
  //   _h2Consequent = h2->getConsequent();

  // for(std::vector<EquationTerm>::iterator equation_iterator = _h2Antecedent.begin();
  //     equation_iterator != _h2Antecedent.end(); ++equation_iterator){
  //   if(*equation_iterator != _h1Consequent)
  //     _h1Antecedent.push_back(*equation_iterator);
  // }
  // _h2LocalUf.merge(_h1LocalUf.find(_h1Consequent.first->getId()),
  // 		   _h1LocalUf.find(_h1Consequent.second->getId()));

  // HornClause * hc = new HornClause(_h2LocalUf, _h1Antecedent,
  // 				   _h2Consequent, local_terms);
  // combinationHelper(hc);
}

void HornClauses::mergeType2_1AndType4(HornClause * h1, HornClause * h2){
  // Same as mergeType2_1AndType3
}

void HornClauses::mergeType2AndType2(HornClause * h1, HornClause * h2){
  
  // UnionFind _h1LocalUf = h1->getLocalUF(),
  //   _h2LocalUf = HornClause::getGlobalUF();

  // std::vector<EquationTerm> _h1Antecedent = h1->getAntecedent(),
  //   _h2Antecedent = h2->getAntecedent();
  // EquationTerm _h1Consequent = h1->getConsequent(),
  //   _h2Consequent = h2->getConsequent();
	
  // for(std::vector<EquationTerm>::iterator _it = _h1Antecedent.begin();
  //     _it != _h1Antecedent.end(); ++_it){
  //   if(_h2LocalUf.find(_it->first->getId()) !=
  //      _h2LocalUf.find(_it->second->getId())){
  //     Term * _u = local_terms[_h2LocalUf.find(_it->first->getId())],
  // 	* _v = local_terms[_h2LocalUf.find(_it->second->getId())];
  //     if(*_u >= *_v)
  // 	_h2Antecedent.push_back(std::make_pair(_u, _v));
  //     else
  // 	_h2Antecedent.push_back(std::make_pair(_v, _u));
  //   }
  // }
  
  // Term * _u = local_terms[_h2LocalUf.find(_h1Consequent.first->getId())],
  //   * _v = local_terms[_h2LocalUf.find(_h2Consequent.first->getId())];
  
  // if(*_u >= *_v)
  //   _h2Consequent = std::make_pair(_u, _v);
  // else
  //   _h2Consequent = std::make_pair(_v, _u);
	
  // HornClause * hc = new HornClause(_h2LocalUf, _h2Antecedent,
  // 				   _h2Consequent, local_terms);
  // combinationHelper(hc);
}

void HornClauses::mergeType2AndType3(HornClause * h_left, HornClause * h_right, Term * to_remove){
  auto to_replace = h_left->getConsequent().first->getId() == to_remove->getId() ?
    h_left->getConsequent().second : h_left->getConsequent().first;
  auto consequent = std::make_pair(h_right->getConsequent().first, h_right->getConsequent().second);

  std::vector<EquationTerm> antecedent;
  for(auto equation : h_left->getAntecedent()){
    if(equation.first->getId() == to_remove->getId())
      antecedent.push_back(std::make_pair(equation.second, to_replace));
    else{
      if(equation.second->getId() == to_remove->getId())
      antecedent.push_back(std::make_pair(equation.first, to_replace));
      else
	antecedent.push_back(equation);
    }
  }
  
  for(auto equation : h_right->getAntecedent()){
    if(equation.first->getId() == to_remove->getId())
      antecedent.push_back(std::make_pair(equation.second, to_replace));
    else{
      if(equation.second->getId() == to_remove->getId())
      antecedent.push_back(std::make_pair(equation.first, to_replace));
      else
	antecedent.push_back(equation);
    }
  }

  HornClause * hc = new HornClause(auxiliar_cc, antecedent, consequent);
  combinationHelper(hc);
}

void HornClauses::mergeType2AndType4(HornClause * h1, HornClause * h2){
  // Same as mergeType2AndType3
}

void HornClauses::combinationHelper(HornClause * hc){
  auxiliar_cc.transferEqClassAndPreds(original_cc);
  
  if(hc->checkTriviality(original_cc.getEquivalenceClass())){
    delete hc;
#if DEBUG_COMBINATION_HELPER
    std::cout << "Inside combination helper: " << *hc << " was deleted" << std::endl << std::endl;
#endif
    return;
  }
  
#if DEBUG_COMBINATION_HELPER
  std::cout << "Inside combination helper: " << *hc << " was added!" << std::endl << std::endl;
#endif
  
  horn_clauses.push_back(hc);
  // makeMatches is called for all the additions
  // done by combinationHelper inside
  // HornClauses::conditionalElimination
}

unsigned HornClauses::size(){
  return horn_clauses.size();
}

std::vector<HornClause*> HornClauses::getHornClauses(){
  std::vector<HornClause*> new_hcs;
  for(auto it : horn_clauses){
    auto consequent = it->getConsequent();
    if(it->getAntecedentCommon()
       && consequent.first->getSymbolCommonQ()
       && consequent.second->getSymbolCommonQ())
      new_hcs.push_back(it);
  }
  return new_hcs;
}

std::vector<HornClause*> HornClauses::getReducibleHornClauses(){
  std::vector<HornClause*> new_hcs;
  for(auto it : reduced)
    for(unsigned index = 0; index < reduced_length[it.first]; ++index)
      new_hcs.push_back(horn_clauses[it.second[index]]);
  return new_hcs;
}

template<typename A>
void HornClauses::swap(std::vector<A> & a, unsigned i, unsigned j){
  A temp = a[i];
  a[i] = a[j];
  a[j] = temp;
}

std::ostream & HornClauses::printMatch1(std::ostream & os, Match1 & m1){
  for(auto term_it : m1){
    os << term_it.first->to_string()
       << std::endl;
    for(auto position : m1[term_it.first])
      os << position << " ";
    os << std::endl;
  }
  return os;
}

std::ostream & HornClauses::printMatch2(std::ostream & os, Match2 & m2){
  for(auto equation_it : m2){
    os << equation_it.first.first->to_string()
       << " = " << equation_it.first.second->to_string()
       << std::endl;
    for(auto position : m2[equation_it.first])
      os << position << " ";
    os << std::endl;
  }
  return os;
}

std::ostream & operator << (std::ostream & os, const HornClauses & hcs){
  int i = 1;
  for(auto it : hcs.horn_clauses){
    os << i << ". " << *it << std::endl;
    ++i;
  }
  return os;
}
