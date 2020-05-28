#ifndef _UTIL_
#define _UTIL_

#include <z3++.h>
#include <vector>

bool compareEquation(const z3::expr &, const z3::expr &);
bool compareTerm(const z3::expr &, const z3::expr &);

template<typename T>
std::vector<std::vector<T>> GeneralizedCartesianProduct(std::vector<std::vector<T>> const & x){
  unsigned ans_size = 1;
  for(auto const & entry : x)
    ans_size *= entry.size();

  std::vector<std::vector<T>> ans(ans_size, std::vector<T>(0));

  for(auto const & entry : x){
    auto block_size = ans_size/entry.size();
    unsigned i = 1;
    unsigned j = 0;
    for(auto const & value : entry){
      while(j < i*block_size){
        ans[j].push_back(value);
        ++j;
      }
      ++i;
    }
  }

  return ans;
}

template<typename T>
void printGeneralizedCartesianProduct(std::vector<std::vector<T>> const & x){
  for(auto const & entry : x){
    for(auto const & value : entry)
      std::cout << value << " ";
    std::cout << std::endl;
  }
}
#endif

