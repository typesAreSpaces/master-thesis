#include <iostream>
#include "Octagon.h"

int main(){

  Octagon test1(NEG, 1, ZERO, 0);
  Octagon test2(POS, 10, NEG, 5);
  Octagon test3(NEG, 3, ZERO, 0);
  Octagon test5(POS, 120, POS, 13);
  Octagon test6(NEG, 120, POS, 13);
  Octagon test7(POS, 3, POS, 2);
  Octagon test8(ZERO, 0, ZERO, 0);
  std::cout << test1 << std::endl;
  std::cout << test2 << std::endl;
  std::cout << test3 << std::endl;
  std::cout << test5 << std::endl;
  std::cout << test6 << std::endl;
  std::cout << test7 << std::endl;
  std::cout << test8 << std::endl;

  Octagon _test1(1);
  Octagon _test2(0);
  Octagon _test3(2);
  std::cout << _test1 << std::endl;
  std::cout << _test2 << std::endl;
  std::cout << _test3 << std::endl;
  return 0;
}
