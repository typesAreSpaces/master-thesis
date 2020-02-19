#ifndef _EUF_INTERPOLANT_
#define _EUF_INTERPOLANT_

#include <set>
#include <map>
#include "HornClauses.h"

typedef std::map<std::string, std::vector<unsigned> > UncommonPositions;

class EUFInterpolant {

  z3::context &     ctx;
  unsigned          min_id;
  z3::expr_vector   subterms; // <--- Note: elements below min_id are undefined
  UncommonPositions uncommon_positions;
  UnionFind         uf;
  HornClauses       horn_clauses;

  // The following function defines (partially) horn_clauses, subterms, and uncommon_positions.
  void              init(z3::expr const &, unsigned &, std::vector<bool> &);
  z3::expr_vector   buildHCBody(z3::expr const &, z3::expr const &);
  // The following function adds more elements to horn_clauses. horn_clauses are totally defined now.
  void              exposeUncommons();
  z3::expr_vector   conditionalReplacement(z3::expr_vector &); // Pending (1)
  z3::expr_vector   substitutions(z3::expr &, z3::expr &, z3::expr_vector &); // (??)
  
 public:
  EUFInterpolant(z3::expr const &);
  ~EUFInterpolant();
  z3::expr              buildInterpolant(); // Pending (2)
  friend std::ostream & operator << (std::ostream &, EUFInterpolant &);
};

#endif
