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

class EUFInterpolant {
  
  unsigned original_num_terms;
  
  z3::context &   ctx;
  Z3Subterms      subterms;
  z3::expr        contradiction;
  z3::expr_vector disequalities;
  
  FSymPositions    fsym_positions;
  UnionFindExplain ufe;
  HornClauses      horn_clauses;

  IdsToMerge ids_to_merge;

  CurryDeclarations        curry_decl;  
  FactoryCurryNodes        factory_curry_nodes;
  CongruenceClosureExplain cc;

  unsigned        maxIdFromAssertions(z3::expr_vector const &);
  void            init(z3::expr_vector const &);
  void            initFormula(z3::expr const &);

  z3::expr        repr(const z3::expr &);

  z3::expr_vector buildHCBody(z3::expr const &, z3::expr const &);
  void            disequalitiesToHCS();

  void            exposeUncommons();
  z3::expr_vector conditionalReplacement(z3::expr_vector &);                // TODO:
  z3::expr_vector substitutions(z3::expr &, z3::expr &, z3::expr_vector &); // TODO:
  
 public:
  EUFInterpolant(z3::expr_vector const &);
  ~EUFInterpolant();
  z3::expr              buildInterpolant(std::vector<Replacement>);  // TODO:
  friend std::ostream & operator << (std::ostream &, EUFInterpolant &);
};

#endif
