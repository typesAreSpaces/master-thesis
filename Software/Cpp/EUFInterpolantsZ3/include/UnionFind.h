#ifndef UNIONFIND_H
#define UNIONFIND_H

#include <iostream>
#include <vector>
#include <cassert>
#include <list>

typedef std::vector<std::list<unsigned> > PredList;

class UnionFind {
  
protected:
  std::vector<unsigned> representative;
  std::vector<unsigned> rank;
  unsigned size;
  
public:
  UnionFind();
  UnionFind(unsigned);
  UnionFind(unsigned [], unsigned);
  UnionFind(const UnionFind &);
  virtual ~UnionFind();
  virtual void combine(unsigned, unsigned);
  virtual void merge(unsigned, unsigned);
  virtual void link(unsigned, unsigned);
  virtual unsigned find(unsigned);
  bool greater(unsigned, unsigned);
  class iterator {
    UnionFind * m_uf;
    unsigned    m_element;
    unsigned    m_index;
  public:
    iterator(UnionFind * m_uf, unsigned m_element, unsigned m_index) :
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
  virtual void resize(unsigned);
  virtual bool operator ==(const UnionFind &);
  const unsigned getSize() const { return size; }
  const unsigned getRank(unsigned i) { return rank[find(i)]; }
  friend std::ostream & operator << (std::ostream &, UnionFind &);
};

#endif
