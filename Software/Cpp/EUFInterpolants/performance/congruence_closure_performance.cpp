#include <iostream>
#include <fstream>
#include <cstdlib>
#include <ctime>

#include "CongruenceClosure.h"

int main(int argc, char ** argv){
	
	// Testing CongruenceClosure algortihm's performance
	std::ifstream example(argv[1]);
	clock_t begin = clock();
	CongruenceClosure congruence_closure_test(example);
	congruence_closure_test.algorithm();
	clock_t end = clock();
	std::cout << double(end - begin) / CLOCKS_PER_SEC << std::endl;
	
  return 0;
}
