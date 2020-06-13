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
  std::cout << std::endl;

  for(unsigned i = 0; i < 4294967295; i++){
    Octagon oct(i);
    assert(oct.getUtviPosition() == i);
  }

  return 0;
}
