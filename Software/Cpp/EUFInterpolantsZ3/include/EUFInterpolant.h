#ifndef _EUF_INTERPOLANT_
#define _EUF_INTERPOLANT_

#include <map>
#include <list>
#include "HornClauses.h"
#include "Hornsat.h"

typedef std::map<std::string, std::vector<unsigned> > FSymPositions;
typedef std::vector<std::list<unsigned> > CCList;

class EUFInterpolant {

  z3::context &     ctx;
  unsigned          min_id;
  // Note: elements below min_id are undefined
  z3::expr_vector   subterms;
  FSymPositions     fsym_positions;
  UnionFind         uf;
  HornClauses       horn_clauses;
  z3::expr          contradiction;
  z3::expr_vector   disequalities;
  unsigned          original_num_terms;
  CCList            cc_list;
  

  // The following function defines (partially) horn_clauses, subterms, and uncommon_positions.
  void            init(z3::expr const &, unsigned &, std::vector<bool> &);
  void            initCCList(z3::expr const &);
  void            processEqs(z3::expr const &);
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
