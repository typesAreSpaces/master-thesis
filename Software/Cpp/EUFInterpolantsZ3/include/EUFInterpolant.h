#ifndef _EUF_INTERPOLANT_
#define _EUF_INTERPOLANT_

#include <map>
#include "Hornsat.h"
#include "CurryNode.h"

template<typename T>
void insert(std::list<T> & l, T element){
  if(!std::binary_search(l.begin(), l.end(), element))
    l.insert(std::lower_bound(l.begin(), l.end(), element), element);
  return;
}

typedef std::map<std::string, std::vector<unsigned> > FSymPositions;
typedef std::vector<std::list<unsigned> > CCList;
typedef std::map<unsigned, CurryNode*> CurryDeclarations;
typedef std::vector<CurryNode*>        CurryNodes;

class EUFInterpolant {
  
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
  CCList            pred_list;
  
  CurryNodes        curry_nodes;
  CurryNodes        extra_nodes;
  CurryDeclarations curry_decl;

  void            init(z3::expr const &, unsigned &, std::vector<bool> &);
  void            curryfication(z3::expr const &, std::vector<bool> &);
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
