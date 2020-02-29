#ifndef UNIONFINDEXPLAIN_H
#define UNIONFINDEXPLAIN_H

#include <iostream>
#include <vector>
#include <list>
#include <cassert>
#include <unordered_map>
 
struct ExplainEquation {
  unsigned source, target;
  
  ExplainEquation(unsigned source, unsigned target) :
    source(source), target(target) {}
  
  friend std::ostream & operator << (std::ostream & os, const ExplainEquation & eq){
    os << eq.source << " := " << eq.target;
    return os;
  }
};

typedef std::list<ExplainEquation> ExplainEquations;
 
class UnionFindExplain {
  
  std::hash<unsigned> hasher;
  std::vector<unsigned> representative;
  std::vector<unsigned> rank;
  std::vector<unsigned> forest;
  std::vector<ExplainEquation> records;
  std::vector<ExplainEquation> inserted_equations;
  std::unordered_map<std::size_t, unsigned> path;
  unsigned size, global_ticket;

  std::size_t hash_combine(unsigned, unsigned);
  void explainHelper(unsigned, unsigned, ExplainEquations &);
  
public:
  UnionFindExplain();
  UnionFindExplain(unsigned);
  UnionFindExplain(const UnionFindExplain &);
  ~UnionFindExplain();
  void combine(unsigned, unsigned);
  void merge(unsigned, unsigned);
  void link(unsigned, unsigned);
  unsigned find(unsigned);
  bool greater(unsigned, unsigned);
  ExplainEquations explain(unsigned, unsigned);
  class iterator {
    UnionFindExplain * m_uf;
    unsigned    m_element;
    unsigned    m_index;
  public:
    iterator(UnionFindExplain * m_uf, unsigned m_element, unsigned m_index) :
      m_uf(m_uf), m_element(m_element), m_index(m_index){}
    bool operator ==(iterator const & other) { return m_element == other.m_element && m_index == other.m_index; }
    bool operator !=(iterator const & other) { return m_element != other.m_element || m_index != other.m_index; }
    iterator & operator ++(){
      m_index++;
      while(m_index < m_uf->size && m_uf->find(m_index) != m_element) m_index++;
      return *this;
    }
    unsigned operator *(){ return m_index; }
  };
  iterator begin(unsigned m_element){
    auto r = iterator(this, m_element, 0);
    if(find(0) != m_element) ++r;
    return r;
  }
  iterator end(unsigned m_element){ return iterator(this, m_element, size); }
  void increaseSize(unsigned);
  bool operator ==(const UnionFindExplain &);
  friend std::ostream & operator << (std::ostream &, const UnionFindExplain &);
};

#endif
