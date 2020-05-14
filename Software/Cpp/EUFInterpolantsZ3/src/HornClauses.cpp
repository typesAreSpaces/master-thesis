#include "HornClauses.h"
#define DEBUG_HORN_CLAUSES       0
#define DEBUG_ADDINGHC           0
#define DEBUG_MAKE_MATCHES       0
#define DEBUG_CE                 0
#define DEBUG_COMBINATION_HELPER 0
#define DEBUG_MATCHES            0
#define DEBUG_DESTRUCTOR_HCS     0

HornClauses::HornClauses(UnionFindExplain & ufe) : ufe(ufe) {}

HornClauses::~HornClauses(){
  for(auto it : horn_clauses)
    delete it;
#if DEBUG_DESTRUCTOR_HCS
  std::cout << "Done ~HornClauses" << std::endl;
#endif
}

// This procedure removes
// unnecessayr Horn Clauses.
// It implements the following rule:
// C, D -> a     C -> a
// ---------------------
//       C -> a
void HornClauses::simplifyHornClauses(){
  throw "HornClauses::simplifyHornClauses not implemented yet!";
  //unsigned position = 0;
  //bool       change = true;

  //// Filter: Only Type 2 or Type 2.1 are allowed here		
  //for(auto it : horn_clauses){	
  //if(it->isCommonAntecedent()
  //&& it->isCommonConsequent()){
  //reduced[it->getConsequent()].push_back(position);
  //}
  //++position;
  //}

  //for(auto horn_clause : reduced){
  //unsigned num_of_positions = horn_clause.second.size();
  //for(unsigned i = 0; i + 1 < num_of_positions; ++i){
  //unsigned j = i + 1;
  //while(change && j < num_of_positions){
  //change = false;
  //unsigned i_position = horn_clause.second[i],
  //j_position = horn_clause.second[j],
  //last_position = horn_clause.second[num_of_positions - 1];

  //if(*horn_clauses[i_position] > *horn_clauses[j_position]){
  //change = true;
  //swapHornClauses(j_position, last_position);
  //--num_of_positions;
  //}
  //else{
  //if(*horn_clauses[i_position] < *horn_clauses[j_position]){
  //change = true;
  //swapHornClauses(i_position, j_position);
  //swapHornClauses(j_position, last_position);
  //--num_of_positions;
  //}
  //else
  //++j; 
  //}
  //}
  //}
  //reduced_length[horn_clause.first] = num_of_positions;
  //}
}

void HornClauses::swapHornClauses(unsigned i, unsigned j){
  auto temp = horn_clauses[i];
  horn_clauses[i] = horn_clauses[j];
  horn_clauses[j] = temp;
  return;
}

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
    case Z3_OP_FALSE:
      horn_clauses.push_back(hc);
      curr_num_horn_clauses++;
      return;
    default: 
      throw "Problem @ HornClauses::add. The consequent of HornClause * hc is neither an equation nor a false constant";
  }
}

void HornClauses::conditionalElimination(std::vector<Replacement> replacements){
  throw "HornClauses::conditionalElimination not implemented yet!";
#if DEBUG_CE
  std::cout << "Horn Clauses produced - after simplify:" << std::endl;
#endif 
}

unsigned HornClauses::size() const { return horn_clauses.size(); }

const std::vector<HornClause*> & HornClauses::getHornClauses() const { return horn_clauses; }

HornClause* HornClauses::operator[](unsigned i) const { return horn_clauses[i]; }

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
