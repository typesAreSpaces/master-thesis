#include "DisjEqsPropagator.h"
#include <z3++.h>

DisjEqsPropagator::DisjEqsPropagator(std::vector<z3::expr> const & elements) : 
  equalities(),
  size(elements.size()*(elements.size() - 1)/2), subset_size_query(0),
  current_combination(), result(),
  iterator_state()
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
  iterator_state.clear();
  current_combination.clear();

  if(!subset_size)
    return;

  subset_size_query = subset_size;
  for(unsigned i = 0; i < size; ++i)
    iterator_state.push_back({i, subset_size - 1});
}

bool DisjEqsPropagator::next(){
  while(!iterator_state.empty()){
    auto current_state = iterator_state[0];
    iterator_state.pop_front();

    unsigned current_index = current_state.first, 
             current_subset_size = current_state.second,
             current_level = subset_size_query - current_subset_size;

    while(current_combination.size() >= current_level)
      current_combination.pop_back();
    current_combination.push_back(equalities[current_index]);
    
    if(current_subset_size == 0)
      return true;

    for(unsigned index = current_index + 1; index < size; ++index)
      iterator_state.push_front({index, current_subset_size - 1});
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
