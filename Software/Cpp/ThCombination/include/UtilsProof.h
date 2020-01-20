#ifndef _UTIL_
#define _UTIL_

#include <iostream>
#include <z3++.h>
#include <vector>

void addConjunction(z3::solver &, z3::expr const &);
bool earlyExit(std::vector<bool> &, z3::expr const &);
void extractHypothesisFromProof(z3::expr const &);
z3::expr_vector collectEqualitiesFromProof(z3::expr const &);
void collectEqualitiesFromProofAux(std::vector<bool> &,
				   std::vector<bool> &,
				   z3::expr_vector &,
				   z3::expr const &);
#endif
