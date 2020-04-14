#ifndef _EUF_INTERPOLANT_
#define _EUF_INTERPOLANT_

#include <map>
#include "Hornsat.h"
#include "CongruenceClosureExplain.h"
#include "CurryNode.h"

template<typename T>
void insert(std::list<T> & l, T element){
  if(!std::binary_search(l.begin(), l.end(), element))
    l.insert(std::lower_bound(l.begin(), l.end(), element), element);
  return;
}

typedef std::map<std::string, std::vector<unsigned> > FSymPositions;

struct Z3Subterms {
  z3::expr_vector subterms;
  std::vector<bool> visited;
  
  Z3Subterms(z3::context & ctx) : subterms(ctx), visited() {}

  class iterator {
    const Z3Subterms * m_subterms;
    unsigned m_index;
    public:
    iterator(const Z3Subterms * s, unsigned i): m_subterms(s), m_index(i) {}
    iterator operator=(const iterator & other) {
      m_subterms = other.m_subterms;
      m_index = other.m_index;
      return *this;
    }
    bool operator==(const iterator & other) const { 
      return other.m_index == m_index;
    }
    bool operator!=(const iterator & other) const { 
      return other.m_index != m_index;
    }
    iterator & operator++() {
      ++m_index;
      return *this;
    }
    z3::expr operator*() const {
      return (m_subterms->subterms)[m_index];
    }
  };

  iterator begin() const { return iterator(this, 0); }
  iterator end() const { return iterator(this, subterms.size()); }
};

class EUFInterpolant {
  
  unsigned min_id;
  unsigned original_num_terms;
  
  z3::context &   ctx;
  // Note: elements below min_id are undefined
  z3::expr_vector subterms;
  z3::expr        contradiction;
  z3::expr_vector disequalities;
  
  FSymPositions    fsym_positions;
  UnionFindExplain uf;
  PredList         pred_list;
  HornClauses      horn_clauses;

  CurryDeclarations curry_decl;  
  FactoryCurryNodes factory_curry_nodes;

  void            init(z3::expr const &, unsigned &, std::vector<bool> &);
  void            initPredList(z3::expr const &);
  void            processEqs(z3::expr const &);
  void            processEqs(z3::expr const &, CongruenceClosureNO &);
  z3::expr        repr(const z3::expr &);
  z3::expr_vector buildHCBody(z3::expr const &, z3::expr const &);
  void            disequalitiesToHCS();
  void            exposeUncommons();
  z3::expr_vector conditionalReplacement(z3::expr_vector &);                // TODO:
  z3::expr_vector substitutions(z3::expr &, z3::expr &, z3::expr_vector &); // TODO:
  
 public:
  EUFInterpolant(z3::expr const &);
  ~EUFInterpolant();
  z3::expr              buildInterpolant(std::vector<Replacement>);  // TODO:
  friend std::ostream & operator << (std::ostream &, EUFInterpolant &);     // TEMP:
};

#endif
