#ifndef _UTIL_
#define _UTIL_

#include <iostream>
#include <cstring>
#include "z3++.h"
#include "z3.h"

void proveFromFile(std::string);
void interpolantFromFile(std::string);
void interface();
void testSMT2(int, char **);

#endif 
