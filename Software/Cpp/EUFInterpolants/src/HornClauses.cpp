#include "HornClauses.h"
#define debugHornClauses false

unsigned HornClauses::num_horn_clauses = 0;

HornClauses::HornClauses(std::vector<Vertex*> & terms) : local_terms(terms) {
}

HornClauses::~HornClauses(){
  for(std::vector<HornClause*>::iterator it = horn_clauses.begin();
      it != horn_clauses.end(); ++it)
    delete *it;
}

void HornClauses::addHornClause(UnionFind & uf,
								Vertex* u, Vertex* v,
								bool is_disequation){
  HornClause * hc = new HornClause(uf, u, v, local_terms, is_disequation);
  if(!is_disequation){
	hc->normalize();
	if(hc->checkTriviality()){
	  delete hc;
	  return;
	}
  }
  horn_clauses.push_back(hc);
  makeMatches(hc, num_horn_clauses);
  ++num_horn_clauses;
}

void HornClauses::addHornClause(UnionFind & uf,
								std::vector<equality> & antecedent,
								equality & consequent,
								bool is_disequation){
  HornClause * hc = new HornClause(uf, antecedent, consequent, local_terms);
  if(!is_disequation){
	hc->normalize();
	if(hc->checkTriviality()){
	  delete hc;
	  return;
	}
  }
  horn_clauses.push_back(hc);
  makeMatches(hc, num_horn_clauses);
  ++num_horn_clauses;
}

void HornClauses::conditionalElimination(){
  bool change = true;
  SetOfUnsignedPairs prev_combinations;
	
  while(change){
		
    change = false;
	unsigned oldSize = horn_clauses.size(), newSize;

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
    mc1ConsequentAndmc1Antecedent2(prev_combinations, change);
		
	// Update the match data structures
	newSize = horn_clauses.size();
	mc1_antecedent.clear();
	mc1_consequent.clear();
	mc2_antecedent.clear();
	mc2_consequent.clear();
	for(unsigned i = oldSize; i < newSize; ++i)
	  makeMatches(horn_clauses[i], i);
  }

  simplify();
 
  if(debugHornClauses){
	std::cout << "Horn Clauses produced:" << std::endl;
	for(match2::iterator it = reduced.begin(); it != reduced.end(); ++it)
	  for(unsigned i = 0; i < reduced_length[it->first] + 1; ++i)
		std::cout << *horn_clauses[it->second[i]] << std::endl;
  }
}

void HornClauses::mc2ConsequentAndmc2Antecedent(SetOfUnsignedPairs & prev_combinations,
												bool & change){
  for(auto map_equality_positions = mc2_consequent.begin();
	  map_equality_positions != mc2_consequent.end(); ++map_equality_positions){
	auto equality = map_equality_positions->first;
	auto positions_consequent = map_equality_positions->second;
	for(unsigned position_consequent : positions_consequent)
	  for(unsigned position_antecedent : mc2_antecedent[equality]){
		if(existential(prev_combinations, std::make_pair(position_consequent,
														 position_antecedent))
		   && existential(prev_combinations, std::make_pair(position_antecedent,
															position_consequent))){
		  if(debugHornClauses)
			std::cout << "1. Combine " << std::endl
					  << *horn_clauses[position_consequent] << std::endl
					  << " with " << std::endl << *horn_clauses[position_antecedent]
					  << std::endl;
		  prev_combinations.insert(std::make_pair(position_consequent,
												  position_antecedent));
		  mergeType2_1AndType3(horn_clauses[position_consequent],
							   horn_clauses[position_antecedent]);
		  if(change)
			std::cout << "Something happened in 1" << std::endl;
		}
	  }
  }
}

void HornClauses::mc1ConsequentAndmc1Antecedent(SetOfUnsignedPairs & prev_combinations,
												bool & change){
  for(auto map_vertex_positions = mc1_consequent.begin();
	  map_vertex_positions != mc1_consequent.end(); ++map_vertex_positions){
		
	auto vertex = map_vertex_positions->first;
	auto positions_consequent = map_vertex_positions->second;
	for(unsigned position_consequent : positions_consequent){
			
	  for(unsigned position_antecedent : mc1_antecedent[vertex]){
		if(existential(prev_combinations, std::make_pair(position_consequent,
														 position_antecedent))
		   &&
		   existential(prev_combinations, std::make_pair(position_antecedent,
														 position_consequent))
		   && horn_clauses[position_consequent]->getAntecedentValue()){
		  if(debugHornClauses)
			std::cout << "2. Combine " << position_consequent << " , "
					  << position_antecedent << std::endl
					  << *horn_clauses[position_consequent] << std::endl
					  << " with " << std::endl << *horn_clauses[position_antecedent]
					  << std::endl;
		  prev_combinations.insert(std::make_pair(position_consequent,
												  position_antecedent));
		  mergeType2AndType3(horn_clauses[position_consequent],
							 horn_clauses[position_antecedent]);
		  if(change)
			std::cout << "Something happened in 2" << std::endl;
		}
	  }
	}
  }
}

void HornClauses::mc1ConsequentAndmc2Antecedent(SetOfUnsignedPairs & prev_combinations,
												bool & change){
  for(match1::iterator map_vertex_positions_consequent = mc1_consequent.begin();
	  map_vertex_positions_consequent != mc1_consequent.end();
	  ++map_vertex_positions_consequent){
		
	auto vertex_consequent = map_vertex_positions_consequent->first;
	auto positions_consequent = map_vertex_positions_consequent->second;
	for(unsigned position_consequent :positions_consequent){
			
	  for(match2::iterator map_equality_positions_antecedent = mc2_antecedent.begin();
		  map_equality_positions_antecedent != mc2_antecedent.end();
		  ++map_equality_positions_antecedent){
		auto equality_antecedent = map_equality_positions_antecedent->first;
		auto positions_antecedent = map_equality_positions_antecedent->second;
		if(equality_antecedent.first == vertex_consequent ||
		   equality_antecedent.second == vertex_consequent)
		  for(unsigned position_antecedent : mc2_antecedent[equality_antecedent]){
			if(existential(prev_combinations, std::make_pair(position_consequent,
															 position_antecedent))
			   &&
			   existential(prev_combinations, std::make_pair(position_antecedent,
															 position_consequent))
			   && horn_clauses[position_consequent]->getAntecedentValue()){
			  if(debugHornClauses)
				std::cout << "3. Combine " << std::endl
						  << *horn_clauses[position_consequent] << std::endl
						  << " with " << std::endl
						  << *horn_clauses[position_antecedent]
						  << std::endl;
			  prev_combinations.insert(std::make_pair(position_consequent,
													  position_antecedent));
			  mergeType2AndType3(horn_clauses[position_consequent],
								 horn_clauses[position_antecedent]);
			  if(change)
				std::cout << "Something happened in 3" << std::endl;
			}
		  }
	  }
	}
  }
}

void HornClauses::mc1ConsequentAndmc1Antecedent2(SetOfUnsignedPairs & prev_combinations,
												 bool & change){
  for(match1::iterator map_vertex_positions = mc1_consequent.begin();
	  map_vertex_positions != mc1_consequent.end(); ++map_vertex_positions){
		
	auto vertex_consequent_1 = map_vertex_positions->first;
	auto positions_consequent_1 = map_vertex_positions->second;
	for(unsigned position_consequent_1 : positions_consequent_1)
			
	  for(unsigned position_consequent_2 : mc1_consequent[vertex_consequent_1]){
		if(existential(prev_combinations, std::make_pair(position_consequent_1,
														 position_consequent_2))
		   &&
		   existential(prev_combinations, std::make_pair(position_consequent_2,
														 position_consequent_1))
		   && horn_clauses[position_consequent_1]->getAntecedentValue()
		   && horn_clauses[position_consequent_2]->getAntecedentValue()){
		  if(debugHornClauses)
			std::cout << "4. Combine " << std::endl
					  << *horn_clauses[position_consequent_1] << std::endl
					  << " with " << std::endl << *horn_clauses[position_consequent_2]
					  << std::endl;
		  prev_combinations.insert(std::make_pair(position_consequent_1,
												  position_consequent_2));
		  mergeType2AndType2(horn_clauses[position_consequent_1],
							 horn_clauses[position_consequent_2]);
		  if(change)
			std::cout << "Something happened in 4" << std::endl;
		}
	  }
  }
}

// This method removes unnecessary extra Horn Clauses
// Implements the following rule:
// C, D -> a     C -> a
// ---------------------
//       C -> a
void HornClauses::simplify(){
  unsigned position = 0;
  bool change = false;
	
  for(std::vector<HornClause*>::iterator it = horn_clauses.begin();
	  it != horn_clauses.end(); ++it){
	// Filter: Only Type 2 or Type 2.1 are allowed here		
	if((*it)->getAntecedentValue()
	   && local_terms[(*it)->getConsequent().first->getId()]->getSymbolCommonQ())
	  reduced[(*it)->getConsequent()].push_back(position);
	++position;
  }

  for(match2::iterator it = reduced.begin();
	  it != reduced.end(); ++it){
	unsigned length = it->second.size();
	for(unsigned i = 0; i + 1 < length; ++i)
	  for(unsigned j = i + 1; j < length; ++j){
		do{
		  if(*horn_clauses[it->second[i]] > *horn_clauses[it->second[j]]){
			swap(horn_clauses, j, length - 1);
			change = true;
			--length;
		  }
		  else if(*horn_clauses[it->second[i]] < *horn_clauses[it->second[j]]){
			swap(horn_clauses, i, j);
			swap(horn_clauses, j, length - 1);
			change = true;
			--length;
		  }
		} while(change && (i < length));
		reduced_length[it->first] = length;
	  }
  }
}

// Precondition: 
// All HornClauses here are assumed to be normalized
// and oriented!
void HornClauses::makeMatches(HornClause * hc, unsigned i){
  std::vector<equality> & hc_antecedent = hc->getAntecedent();
  equality & hc_consequent = hc->getConsequent();
  for(std::vector<equality>::iterator equation_iterator = hc_antecedent.begin();
      equation_iterator != hc_antecedent.end(); ++equation_iterator){
	// Pay attention to this part !!!
	// If the first term is uncommon,
    // then the equality is uncommon due to
    // the normalizing ordering used
    if(!equation_iterator->first->getSymbolCommonQ()){
	  if(debugHornClauses)
		std::cout << *hc << "\n was added to mc2_antecedent" << std::endl;
      mc2_antecedent[std::make_pair(equation_iterator->first,
									equation_iterator->second)].push_back(i);
	}
    else{
      // If the first term is common and
      // the second term is common, then
      // there is nothing to do!
      if(!equation_iterator->second->getSymbolCommonQ()){
		if(debugHornClauses)
		  std::cout << *hc << "\n was added to mc1_antecedent" << std::endl;
		mc1_antecedent[equation_iterator->second].push_back(i);
	  }
    }
  }
  if(!hc_consequent.first->getSymbolCommonQ()){
	if(debugHornClauses)
	  std::cout << *hc << "\n was added to mc2_consequent" << std::endl;
    mc2_consequent[std::make_pair(hc_consequent.first,
								  hc_consequent.second)].push_back(i);
  }
  else{
    // If the first term is common and
    // the second term is common, then
    // there is nothing to do!
    if(!hc_consequent.second->getSymbolCommonQ()){
	  if(debugHornClauses)
		std::cout << *hc << "\n was added to mc1_consequent" << std::endl;
      mc1_consequent[hc_consequent.second].push_back(i);
	}
  }
}

void HornClauses::mergeType2_1AndType3(HornClause * h1, HornClause * h2){
  UnionFind _h1LocalUf = h1->getLocalUF(),
    _h2LocalUf = HornClause::getGlobalUF();
  equality _h1Consequent = h1->getConsequent(),
    _h2Consequent = h2->getConsequent();
  std::vector<equality> _h1Antecedent = h1->getAntecedent(),
    _h2Antecedent = h2->getAntecedent();

  for(std::vector<equality>::iterator equation_iterator = _h2Antecedent.begin();
      equation_iterator != _h2Antecedent.end(); ++equation_iterator){
    if(*equation_iterator != _h1Consequent)
      _h1Antecedent.push_back(*equation_iterator);
  }
  _h2LocalUf.merge(_h1LocalUf.find(_h1Consequent.first->getId()),
				   _h1LocalUf.find(_h1Consequent.second->getId()));

  HornClause * hc = new HornClause(_h2LocalUf, _h1Antecedent,
								   _h2Consequent, local_terms);
  combinationHelper(hc);
}

void HornClauses::mergeType2_1AndType4(HornClause * h1, HornClause * h2){
  // Same as mergeType2_1AndType3
}

void HornClauses::mergeType2AndType2(HornClause * h1, HornClause * h2){
  UnionFind _h1LocalUf = h1->getLocalUF(),
    _h2LocalUf = HornClause::getGlobalUF();
  equality _h1Consequent = h1->getConsequent(),
    _h2Consequent = h2->getConsequent();
  std::vector<equality> _h1Antecedent = h1->getAntecedent(),
    _h2Antecedent = h2->getAntecedent();
	
  for(std::vector<equality>::iterator _it = _h1Antecedent.begin();
      _it != _h1Antecedent.end(); ++_it){
	if(_h2LocalUf.find(_it->first->getId()) !=
	   _h2LocalUf.find(_it->second->getId())){
	  Vertex * _u = local_terms[_h2LocalUf.find(_it->first->getId())],
		* _v = local_terms[_h2LocalUf.find(_it->second->getId())];
	  if(*_u >= *_v)
		_h2Antecedent.push_back(std::make_pair(_u, _v));
	  else
		_h2Antecedent.push_back(std::make_pair(_v, _u));
	}
  }
  Vertex * _u = local_terms[_h2LocalUf.find(_h1Consequent.first->getId())],
	* _v = local_terms[_h2LocalUf.find(_h2Consequent.first->getId())];
  if(*_u >= *_v)
	_h2Consequent = std::make_pair(_u, _v);
  else
	_h2Consequent = std::make_pair(_v, _u);
	
  HornClause * hc = new HornClause(_h2LocalUf, _h2Antecedent,
								   _h2Consequent, local_terms);
  combinationHelper(hc);
}

void HornClauses::mergeType2AndType3(HornClause * h1, HornClause * h2){
  UnionFind _h1LocalUf = h1->getLocalUF(),
    _h2LocalUf = HornClause::getGlobalUF();
  equality _h1Consequent = h1->getConsequent(),
    _h2Consequent = h2->getConsequent();
  std::vector<equality> _h1Antecedent = h1->getAntecedent(),
    _h2Antecedent = h2->getAntecedent();
	
  for(std::vector<equality>::iterator _it = _h2Antecedent.begin();
      _it != _h2Antecedent.end(); ++_it){
	if(_it->first->getId() == _h1Consequent.second->getId())
	  _it->first = _h1Consequent.first;
	if(_it->second->getId() == _h1Consequent.second->getId())
	  _it->second = _h1Consequent.first;
	_h1Antecedent.push_back(*_it);
  }
  _h2LocalUf.merge(_h1LocalUf.find(_h1Consequent.first->getId()),
				   _h1LocalUf.find(_h1Consequent.second->getId()));

  HornClause * hc = new HornClause(_h2LocalUf, _h1Antecedent,
								   _h2Consequent, local_terms);
  combinationHelper(hc);
}

void HornClauses::mergeType2AndType4(HornClause * h1, HornClause * h2){
  // Same as mergeType2AndType3
}

void HornClauses::combinationHelper(HornClause * hc){
  if(debugHornClauses)
	std::cout << "Temporal Horn Clause " << *hc << std::endl;
  hc->normalize();
  if(debugHornClauses)
	std::cout << "New Horn Clause" << std::endl
			  << *hc << std::endl;
  if(hc->checkTriviality()){
    delete hc;
	if(debugHornClauses)
	  std::cout << "It was deleted" << std::endl << std::endl;
    return;
  }
  if(debugHornClauses)
	std::cout << "It was added!" << std::endl << std::endl;
  orient(hc);
  horn_clauses.push_back(hc);
  ++num_horn_clauses;
}

unsigned HornClauses::size(){
  return num_horn_clauses;
}

std::vector<HornClause*> HornClauses::getHornClauses(){
  std::vector<HornClause*> _hc;
  for(match2::iterator it = reduced.begin(); it != reduced.end(); ++it)
	for(unsigned i = 0; i < reduced_length[it->first] + 1; ++i)
	  _hc.push_back(horn_clauses[it->second[i]]);
  return _hc;
}

void HornClauses::orient(HornClause * hc){
  UnionFind & localUF = HornClause::getGlobalUF();
  std::vector<equality> & antecedent = hc->getAntecedent();
  equality & consequent = hc->getConsequent();
	
  for(std::vector<equality>::iterator _it = antecedent.begin();
	  _it != antecedent.end(); ++_it){
    Vertex * _u = local_terms[localUF.find(_it->first->getId())],
      * _v = local_terms[localUF.find(_it->second->getId())];
    if(*_u >= *_v)
	  *_it = std::make_pair(_u, _v);
	else
	  *_it = std::make_pair(_v, _u);
  }
  Vertex * _u = local_terms[localUF.find(consequent.first->getId())],
    * _v = local_terms[localUF.find(consequent.second->getId())];
  
  if(*_u >= *_v)
	consequent = std::make_pair(_u, _v);
  else
	consequent = std::make_pair(_v, _u);
}

template<typename A>
void HornClauses::swap(std::vector<A> & a, unsigned i, unsigned j){
  A temp = a[i];
  a[i] = a[j];
  a[j] = temp;
}

std::ostream & HornClauses::printMatch1(std::ostream & os, match1 & m1){
  for(match1::iterator _it = m1.begin(); _it != m1.end(); ++_it){
	os << _it->first->to_string() << std::endl;
	for(std::vector<unsigned>::iterator _it2 = m1[_it->first].begin();
		_it2 != m1[_it->first].end(); ++_it2)
	  os << *_it2 << " ";
	os << std::endl;
  }
  return os;
}

std::ostream & HornClauses::printMatch2(std::ostream & os, match2 & m1){
  for(match2::iterator _it = m1.begin(); _it != m1.end(); ++_it){
	os << _it->first.first->to_string()
	   << " = " << _it->first.second->to_string() << std::endl;
	for(std::vector<unsigned>::iterator _it2 = m1[_it->first].begin();
		_it2 != m1[_it->first].end(); ++_it2)
	  std::cout << *_it2 << " ";
	std::cout << std::endl;
  }
  return os;
}

std::ostream & operator << (std::ostream & os, HornClauses & hcs){
  for(std::vector<HornClause*>::iterator _it = hcs.horn_clauses.begin();
      _it != hcs.horn_clauses.end(); ++_it)
	os << **_it << std::endl;
  return os;
}
