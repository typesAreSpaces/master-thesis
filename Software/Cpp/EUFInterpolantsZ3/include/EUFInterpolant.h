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
    unsigned id;
    std::string func_name;
    CurryNode * left, * right;
  public:
    CurryNode(unsigned id) :
      id(id), func_name(""),
      left(nullptr), right(nullptr) {}
    CurryNode(unsigned id, std::string func_name, CurryNode * left, CurryNode * right) :
      id(id), func_name(func_name), left(left), right(right) {}
    CurryNode(const CurryNode & cn) :
      id(cn.id), func_name(cn.func_name), left(cn.left), right(cn.right) {}
    void update(std::string new_name, CurryNode * new_left, CurryNode * new_right){
      func_name = new_name;
      left = new_left;
      right = new_right;
      return;
    }
    friend std::ostream & operator << (std::ostream & os, const CurryNode & cn){
      // TODO: Update this method
      os << cn.func_name;
      if(cn.left != nullptr)
      	os << " Left: " << *cn.left;
      if(cn.right != nullptr)
      	os << " Right: " << *cn.right;
      return os;
    }
  };

  typedef std::map<unsigned, CurryNode*> CurryDeclarations;
  typedef std::vector<CurryNode*>        CurryNodes;
  
  z3::context &     ctx;
  unsigned          min_id;
  // Note: elements below min_id are undefined
  z3::expr_vector   subterms;
  FSymPositions     fsym_positions;
  UnionFindExplain  uf;
  // UnionFind         uf;
  HornClauses       horn_clauses;
  z3::expr          contradiction;
  z3::expr_vector   disequalities;
  unsigned          original_num_terms;
  CCList            cc_list;
  CurryNodes        curry_nodes;
  CurryNodes        extra_nodes;
  CurryDeclarations curry_decl;

  // The following function defines (partially) horn_clauses, subterms, and uncommon_positions.
  void            init(z3::expr const &, unsigned &, std::vector<bool> &);
  void            curryfication(z3::expr const &, CurryNodes &);
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
