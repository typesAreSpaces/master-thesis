#include "Combinatorics.h"
#include <z3++.h>

Combinatorics::Combinatorics(std::vector<z3::expr> const & elements) : 
  elements(elements),
  size(elements.size()), current_combination(), result()
{
}

void Combinatorics::makeCombinationsUtil(unsigned current_index, unsigned subset_size){
  if(!subset_size){
    result.push_back(current_combination);
    return;
  }
  for(unsigned index = current_index; index < size; ++index){
    current_combination.push_back(elements[index]);
    makeCombinationsUtil(index + 1, subset_size - 1);
    current_combination.pop_back();
  }
}

std::vector<std::vector<z3::expr> > Combinatorics::makeCombinations(unsigned subset_size){
  result.clear();
  makeCombinationsUtil(0, subset_size);
  return result;
}

