#include "Match.h"

Match::Match() {}

Match::Match(std::vector<std::vector<unsigned> > m_vec) : m_vec(m_vec) {}

Match::~Match() {
#if DEBUG_DESTRUCTOR_MATCH
  std::cout << "Done ~Match" << std::endl;
#endif
}

unsigned Match::size(){
  return m_vec.size();
}

void Match::push_back(z3::expr const & e, unsigned i){
  if(m_vec.size() <= e.id())
    m_vec.resize(e.id() + 1);
  m_vec[e.id()].push_back(i);
}

std::vector<unsigned> Match::operator [](unsigned i){
  if(i >= m_vec.size())
    m_vec.resize(i + 1);
  return m_vec[i];
}

Match::iterator::iterator(Match * m_vec, unsigned i) : m_vec(m_vec), m_index(i) {}

bool Match::iterator::operator ==(iterator const & other) const {
  return other.m_index == m_index;
}

bool Match::iterator::operator !=(iterator const & other) const {
  return other.m_index != m_index;
}

Match::iterator & Match::iterator::operator ++(){
  ++m_index;
  return *this;
}

std::vector<unsigned> Match::iterator::operator *() const {
  return (*m_vec)[m_index];
}

Match::iterator Match::begin() const { return iterator((Match*)this, 0); }

Match::iterator Match::end() const { return iterator((Match*)this, m_vec.size()); }

std::ostream & operator << (std::ostream & os, const Match & m){
  unsigned i = 0;
  for(auto positions : m.m_vec){
    if(positions.size() > 0){
      os << i << ": ";
      for(auto position : positions)
	os << position << " ";
      os << std::endl;
    }
    i++;
  }
  std::cout << "Total size: " << m.m_vec.size();
  return os;
}
