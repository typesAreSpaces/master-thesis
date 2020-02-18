#ifndef _EUF_INTERPOLANT_
#define _EUF_INTERPOLANT_

#include <set>
#include <map>
#include "HornClauses.h"
#include "UnionFind.h"

typedef std::map<std::string, std::vector<unsigned> > UncommonPositions;

class EUFInterpolant {

  z3::context &     ctx; 
  z3::expr_vector   subterms;
  UncommonPositions uncommon_positions;
  UnionFind         uf;
  HornClauses       horn_clauses;

  void              init(z3::expr const &, unsigned &, std::vector<bool> &);  // Defines: (partially) horn_clauses, subterms, and uncommon_positions.
  void              exposeUncommons(); // Adds more elements to horn_clauses. horn_clauses are totally defined now.
  z3::expr_vector   conditionalReplacement(z3::expr_vector &); // Pending (1)
  z3::expr_vector   substitutions(z3::expr &, z3::expr &, z3::expr_vector &); // (??)
  
 public:
  EUFInterpolant(z3::expr const &);
  ~EUFInterpolant();
  z3::expr              buildInterpolant(); // Pending (2)
  friend std::ostream & operator << (std::ostream &, EUFInterpolant &);
};

#endif
