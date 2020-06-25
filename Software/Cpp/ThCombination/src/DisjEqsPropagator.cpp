#include "DisjEqsPropagator.h"

DisjEqsPropagator::DisjEqsPropagator(z3::expr_vector const & elements) : 
  size(elements.size()*(elements.size() - 1)/2), subset_size_query(0),
  equalities(elements.ctx()), current_disj_eqs(elements.ctx()),
  iterator_state()
{
  for(auto lhs=elements.begin(); lhs!=elements.end(); ++lhs){
    auto rhs=lhs;
    for(++rhs; rhs!=elements.end(); ++rhs)
      equalities.push_back(*lhs == *rhs);
  }
} 

void DisjEqsPropagator::subsetSetup(unsigned subset_size){
  iterator_state.clear();
  current_disj_eqs.resize(0);

  if(!subset_size)
    return;

  subset_size_query = subset_size;
  for(unsigned i = 0; i < size; ++i)
    iterator_state.push_back({i, subset_size - 1});

  // Move to the first element
  hasNext();
}

bool DisjEqsPropagator::hasNext(){
  while(!iterator_state.empty()){
    auto current_state = iterator_state[0];
    iterator_state.pop_front();

    unsigned current_index = current_state.first, 
             current_subset_size = current_state.second,
             current_level = subset_size_query - current_subset_size;

    while(current_disj_eqs.size() >= current_level)
      current_disj_eqs.pop_back();
    current_disj_eqs.push_back(equalities[current_index]);
    
    if(current_subset_size == 0)
      return true;

    for(unsigned index = current_index + 1; index < size; ++index)
      iterator_state.push_front({index, current_subset_size - 1});
  }
  return false;
}

DisjEqsPropagator::DisjEqs DisjEqsPropagator::getCurrentDisjEqs() const {
  return current_disj_eqs;
}

DisjEqsPropagator::iterator::iterator(DisjEqsPropagator * it) : 
  it(it), index_block(0)
{
}

void DisjEqsPropagator::iterator::init(){
  index_block = 1;
  it->subsetSetup(index_block);
}

void DisjEqsPropagator::iterator::operator ++(){
  if(!it->hasNext()){
    it->subsetSetup(++index_block);
    return;
  }
}

bool DisjEqsPropagator::iterator::isLast(){
  return (this->index_block == (it->size + 1));
}

DisjEqsPropagator::DisjEqs DisjEqsPropagator::iterator::operator *() const {
  return it->getCurrentDisjEqs();
}

DisjEqsPropagator::iterator DisjEqsPropagator::begin(){
  auto it = iterator(this);
  it.init();
  return it;
}
