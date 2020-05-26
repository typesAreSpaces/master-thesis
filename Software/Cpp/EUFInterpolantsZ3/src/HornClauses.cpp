#include "HornClauses.h"

HornClauses::HornClauses(UnionFindExplain & ufe) : 
  ufe(ufe), curr_num_horn_clauses(0), max_lit_id(0)
{
}

HornClauses::~HornClauses(){
  for(auto it : horn_clauses)
    delete it.second;
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
  // Group horn clauses by consequent
  // Then make n^2 comparisons per group
  // to determine contaiment relations
  // Select the horn clauses from each 
  // group that are 'minimal' (i.e. they
  // are not contained by another antecedent)

  unsigned position = 0;
  bool     change = true;

  // Filter: Only Type 2 or Type 2.1 are allowed here		
  for(auto it1 : horn_clauses){	
    auto it = it1.second;
    if(it->isCommonAntecedent() && it->isCommonConsequent())
      reduced[it->getConsequent()].push_back(position); // What's reduced? Currently it is not defined
    ++position;
  }

  for(auto horn_clause : reduced){
    unsigned num_of_positions = horn_clause.second.size();
    for(unsigned i = 0; i + 1 < num_of_positions; ++i){
      unsigned j = i + 1;
      while(change && j < num_of_positions){
        change = false;
        unsigned i_position = horn_clause.second[i],
        j_position = horn_clause.second[j],
        last_position = horn_clause.second[num_of_positions - 1];

        if(*horn_clauses[i_position] > *horn_clauses[j_position]){
          change = true;
          swapHornClauses(j_position, last_position);
          --num_of_positions;
        }
        else{
          if(*horn_clauses[i_position] < *horn_clauses[j_position]){
            change = true;
            swapHornClauses(i_position, j_position);
            swapHornClauses(j_position, last_position);
            --num_of_positions;
          }
          else
            ++j; 
        }
      }
    }
    reduced_length[horn_clause.first] = num_of_positions;
  }
}

void HornClauses::swapHornClauses(unsigned i, unsigned j){
  auto temp = horn_clauses[i];
  horn_clauses[i] = horn_clauses[j];
  horn_clauses[j] = temp;
  return;
}

void HornClauses::add(HornClause * hc){
  z3::expr z3_expr_hc = hc->ToZ3Exprc();
  unsigned id = z3_expr_hc.id();
  auto it = horn_clauses.find(id);

  if(it != horn_clauses.end()){
    delete hc;
    return;
  }
  const z3::expr & consequent = hc->getConsequent();
  switch(consequent.decl().decl_kind()){
    case Z3_OP_EQ:
      if(hc->checkTriviality(ufe)){
        delete hc;
        return;
      }
      horn_clauses.insert({id, hc});
      if(max_lit_id < hc->getLocalMaxLitId())
        max_lit_id = hc->getLocalMaxLitId();
      curr_num_horn_clauses++;
      return;
    case Z3_OP_FALSE:
      horn_clauses.insert({id, hc});
      if(max_lit_id < hc->getLocalMaxLitId())
        max_lit_id = hc->getLocalMaxLitId();
      curr_num_horn_clauses++;
      return;
    default: 
      throw "Problem @ HornClauses::add. The consequent of HornClause * hc is neither an equation nor a false constant";
  }
}

unsigned HornClauses::size() const { return horn_clauses.size(); }

HornClause* HornClauses::operator[](unsigned i) const { 
  auto it = horn_clauses.find(i);
  if(it != horn_clauses.end())
    return it->second;
  throw "Problem @ HornClauses::operator[]. Element not found.";
}

std::vector<HornClause *> const HornClauses::getHornClauses() const {
  std::vector<HornClause*> ans;
  ans.reserve(horn_clauses.size());
  for(auto key_value : horn_clauses)
    ans.push_back(key_value.second);
  return ans;
}

unsigned HornClauses::getUFESize() const {
  return ufe.getSize();
}

unsigned HornClauses::getMaxLitId() const {
  return max_lit_id;
}

std::ostream & operator << (std::ostream & os, const HornClauses & hcs){
  unsigned i = 0;
  os << "Horn clauses produced" << std::endl;
  for(auto it : hcs.horn_clauses){
    os << i << ". " << it.second << " " << *(it.second) << std::endl;
    ++i;
  }
  os << "Number of horn clauses: " << i;

  return os;
}
