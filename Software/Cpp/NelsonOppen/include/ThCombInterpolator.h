#ifndef _THCOMB_
#define _THCOMB_
#define _DEBUGEXTPURIFIER_ false

#include "Purifier.h"

class ThCombInterpolator : public Purifier{

  std::vector<bool> visited;
  std::vector<bool> consequent_visited;
  z3::solver        euf_solver;
  z3::solver        oct_solver;
  z3::expr_vector   euf_consequents;
  z3::expr_vector   oct_consequents;

  bool isProvable(z3::solver &, z3::expr const &);
  void addConjunction(z3::solver &, z3::expr const &);
  bool earlyExit(std::vector<bool> &, z3::expr const &);
  void extractHypothesisFromProof(z3::expr const &);
  void collectEqualitiesFromProof(z3::expr const &);
  
public:
  ThCombInterpolator(z3::expr &);
  ~ThCombInterpolator();

  void collectEqualities();
  
  friend std::ostream & operator << (std::ostream &, ThCombInterpolator &);
};

#endif
