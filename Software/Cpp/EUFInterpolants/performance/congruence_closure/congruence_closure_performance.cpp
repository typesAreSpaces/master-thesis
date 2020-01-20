#include <iostream>
#include <fstream>
#include <cstdlib>
#include <ctime>

#include "CongruenceClosure.h"

int main(int argc, char ** argv){
	
  // Testing CongruenceClosure algortihm's performance
  std::string input_info(argv[1]);
  std::ifstream example(input_info);
  clock_t begin = clock();
  CongruenceClosure congruence_closure_test(example);
  congruence_closure_test.algorithm();
  congruence_closure_test.checkCorrectness();
  clock_t end = clock();
  std::cout << input_info.substr(88, input_info.find("_", 88) - 88) << "," << double(end - begin) / CLOCKS_PER_SEC << std::endl;
	
  return 0;
}
