#ifndef _EUF_INTERPOLANT_
#define _EUF_INTERPOLANT_

#include <map>
#include "Hornsat.h"

typedef std::map<std::string, std::vector<unsigned> > FSymPositions;
typedef std::vector<std::list<unsigned> > CCList;

template<typename T>
class UniqueSortedList : public std::list<T> { 
public:
  UniqueSortedList() : std::list<T>(){}
  template<class InputIterator>
  UniqueSortedList(InputIterator first, InputIterator last) : std::list<T>(first, last){}
  void insert(T element){
    if(!std::binary_search(this->begin(), this->end(), element))
      std::list<T>::insert(std::lower_bound(this->begin(), this->end(), element), element);
    return;
  }
};

template<typename T>
void insert(std::list<T> & l, T element){
  if(!std::binary_search(l.begin(), l.end(), element))
    l.insert(std::lower_bound(l.begin(), l.end(), element), element);
  return;
}

class EUFInterpolant {
  class CurryNode {
    std::string func_name;
    CurryNode * rest;
  public:
    CurryNode() :
      func_name(""), rest(nullptr) {}
    CurryNode(std::string func_name, CurryNode * rest) :
      func_name(func_name), rest(rest) {}
    void update(std::string new_name, CurryNode * new_rest) {
      func_name = new_name;
      rest = new_rest;
      return;
    }
    friend std::ostream & operator << (std::ostream & os, const CurryNode & cn){
      os << cn.func_name;
      if(cn.rest != nullptr)
	os << " -> " << *(cn.rest);
      return os;
    }
  };
  
  z3::context &           ctx;
  unsigned                min_id;
  // Note: elements below min_id are undefined
  z3::expr_vector         subterms;
  FSymPositions           fsym_positions;
  UnionFindExplain        uf;
  // UnionFind               uf;
  HornClauses             horn_clauses;
  z3::expr                contradiction;
  z3::expr_vector         disequalities;
  unsigned                original_num_terms;
  CCList                  cc_list;
  std::vector<CurryNode*> curry_nodes;
  

  // The following function defines (partially) horn_clauses, subterms, and uncommon_positions.
  void            init(z3::expr const &, unsigned &, std::vector<bool> &);
  void            curryfication(z3::expr const &, std::vector<CurryNode*> &);
  void            initCCList(z3::expr const &);
  void            processEqs(z3::expr const &);
  void            processEqs(z3::expr const &, CongruenceClosureNO &);
  z3::expr        repr(const z3::expr &);
  z3::expr_vector buildHCBody(z3::expr const &, z3::expr const &);
  void            disequalitiesToHCS();
  void            exposeUncommons();
  // The following function adds more elements to horn_clauses. horn_clauses will be totally defined then.
  z3::expr_vector conditionalReplacement(z3::expr_vector &);                // TODO:
  z3::expr_vector substitutions(z3::expr &, z3::expr &, z3::expr_vector &); // TODO:
  
 public:
  EUFInterpolant(z3::expr const &);
  ~EUFInterpolant();
  z3::expr              buildInterpolant(std::vector<Replacement>);  // TODO:
  friend std::ostream & operator << (std::ostream &, EUFInterpolant &);     // TEMP:
};

#endif
