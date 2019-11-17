#ifndef _GENERATE_
#define _GENERATE_

#define MAX_NUM_INEQUALITIES_RAND 100
#define MAX_NUM_VARS_RAND         90
#define MAX_NUM_ELIM_RAND         10

#include <iostream>
#include <fstream>
#include <cstdlib>
#include <cstdio>
#include <string>

// Generation of random tests

// Writes a random test case, return the
// name of the file generated stored in
// "test/" + eval(generate()) + ".in"
std::string generate();

#endif
