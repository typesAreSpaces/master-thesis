#ifndef PRODUCE_RANDOM
#define PRODUCE_RANDOM

#include <iostream>
#include <fstream>
#include <cstdlib>
#include <ctime>
#include <string>
#include <map>
#include <utility>
#include "GTerms.h"
#include "SignatureTable.h"
#include "Vertex.h"

void generateFile(int, int , int, int, int);
void generateFileAndTest(int, int , int, int, int);
void worstCaseFile(int, int , int, int, int);
void worstCaseFileAndTest(int, int , int, int, int);
void run(int, int , int, int, int);

#endif
