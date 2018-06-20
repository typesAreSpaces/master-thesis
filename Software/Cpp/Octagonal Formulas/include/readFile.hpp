#ifndef _READ_
#define _READ_

#include <iostream>
#include <fstream>
#include <vector>
#include "structures.hpp"

// Reads input file with specific format
// to set up the system of octagonal formulas

void readInput(std::istream &,
	       inequalities &,
	       vi &,
	       positions &,
	       positions &,
	       int &);

#endif
