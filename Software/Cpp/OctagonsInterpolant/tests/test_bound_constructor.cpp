#include <iostream>
#include "Bound.h"

int main(){

  Bound x1(1);
  Bound x2(-12);
  Bound pos_inf(true);
  Bound neg_inf(false);

  std::cout << x1 << std::endl;
  std::cout << x2 << std::endl;
  std::cout << x2 + x1 << std::endl;
  std::cout << x2 - x1 << std::endl;
  std::cout << pos_inf + x2 << std::endl;
  std::cout << neg_inf + x1 << std::endl;
  std::cout << neg_inf << std::endl;
  std::cout << neg_inf + pos_inf << std::endl;
  std::cout << neg_inf - pos_inf << std::endl;

  return 0;
}
