#include "DisjEqsPropagator.h"
#include <z3++.h>

DisjEqsPropagator::DisjEqsPropagator(std::vector<z3::expr> const & elements) : 
  equalities(),
  size(elements.size()*(elements.size() - 1)/2), current_combination(), result()
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
