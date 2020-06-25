#include "DisjEqsPropagator.h"
#include <z3++.h>

DisjEqsPropagator::DisjEqsPropagator(std::vector<z3::expr> const & elements) : 
  equalities(),
  size(elements.size()*(elements.size() - 1)/2), subset_size_query(0),
  current_combination(), result(),
  current_state()
{
  for(auto lhs=elements.begin(); lhs!=elements.end(); ++lhs){
    auto rhs=lhs;
    for(++rhs; rhs!=elements.end(); ++rhs)
      equalities.push_back(*lhs == *rhs);
  }
} 

void DisjEqsPropagator::makeCombinationsUtil(unsigned current_index, unsigned subset_size){
  if(!subset_size){
    result.push_back(current_combination);
    return;
  }
  for(unsigned index = current_index; index < size; ++index){
    current_combination.push_back(equalities[index]);
    makeCombinationsUtil(index + 1, subset_size - 1);
    current_combination.pop_back();
  }
}

DisjEqsPropagator::Combinations DisjEqsPropagator::makeCombinations(unsigned subset_size){
  result.clear();
  makeCombinationsUtil(0, subset_size);
  return result;
}

void DisjEqsPropagator::init(unsigned subset_size){
  current_state.clear();
  subset_size_query = subset_size;
  current_state.push_back({0, subset_size});

}

bool DisjEqsPropagator::next(){
  while(!current_state.empty()){
    auto last_state = current_state[0];
    current_state.pop_front();
    unsigned current_index = last_state.first, 
             current_subset_size = last_state.second;

    // ----------------------------------------------------
    unsigned combination_size = current_combination.size(),
             level = subset_size_query - current_subset_size;

    std::cout << "Level: " << level << std::endl;
    std::cout << "State: " 
      << current_index << ", "
      << current_subset_size << std::endl;
    
    while(combination_size > level){
      combination_size--;
      current_combination.pop_back();
    }
    if(current_index < size)
      current_combination.push_back(equalities[current_index]);
    // ----------------------------------------------------
    
    if(current_subset_size == 0){
      std::cout << "The equations" << std::endl;
      for(auto const & eq : equalities)
        std::cout << eq << " ";
      std::cout << std::endl;
      std::cout << "Current combination" << std::endl;
      for(auto const & x : current_combination)
        std::cout << x << " ";
      std::cout << std::endl;
      return true;
    }

    for(unsigned index = current_index; index < size; ++index)
      current_state.push_front({index + 1, current_subset_size - 1});
  }
  return false;
}

DisjEqsPropagator::Combination DisjEqsPropagator::getCurrentCombination() const {
  return current_combination;
}

DisjEqsPropagator::iterator::iterator(DisjEqsPropagator * it) : 
  it(it), index_block(0), 
  current_block(), current_disj()
{
}

void DisjEqsPropagator::iterator::init(){
  index_block = 1;
  current_block = it->makeCombinations(index_block);
  current_disj = current_block.begin();
}

void DisjEqsPropagator::iterator::next(){
  ++current_disj;
  if(current_disj == current_block.end()){
    current_block = it->makeCombinations(++index_block);
    current_disj = current_block.begin();
    return;
  }
}

void DisjEqsPropagator::iterator::last(){
  index_block = it->size+1;
}

bool DisjEqsPropagator::iterator::isLast(){
  return (this->index_block == (it->size + 1));
}

DisjEqsPropagator::Combination DisjEqsPropagator::iterator::operator *() const {
  return *current_disj;
}

DisjEqsPropagator::iterator DisjEqsPropagator::begin(){
  auto it = iterator(this);
  it.init();
  return it;
}

DisjEqsPropagator::iterator DisjEqsPropagator::end(){
  auto it = iterator(this);
  it.last();
  return it;
}
