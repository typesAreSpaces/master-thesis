#ifndef _UTIL_
#define _UTIL_

#include <z3++.h>
#include <vector>

bool compareEquation(const z3::expr &, const z3::expr &);
bool compareTerm(const z3::expr &, const z3::expr &);

#endif
