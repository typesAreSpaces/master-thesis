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

void generateFile(unsigned, unsigned , unsigned, unsigned, unsigned);
void generateFileAndTest(unsigned, unsigned , unsigned, unsigned, unsigned);
void worstCaseFile(unsigned, unsigned , unsigned, unsigned, unsigned);
void worstCaseFileAndTest(unsigned, unsigned , unsigned, unsigned, unsigned);
void run(unsigned, unsigned , unsigned, unsigned, unsigned);

#endif
