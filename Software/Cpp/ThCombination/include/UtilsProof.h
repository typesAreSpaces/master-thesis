#ifndef _UTIL_
#define _UTIL_

#include <iostream>
#include <z3++.h>
#include <vector>

void addConjunction(z3::solver &, z3::expr const &);
void traverseProof1(z3::expr const &);
void traverseProof2(z3::expr const &);


#endif
