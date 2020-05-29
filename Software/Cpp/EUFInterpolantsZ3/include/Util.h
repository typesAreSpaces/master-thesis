#ifndef _UTIL_
#define _UTIL_

#include <z3++.h>
#include <vector>

bool compareEquation(const z3::expr &, const z3::expr &);
bool compareTerm(const z3::expr &, const z3::expr &);

template<typename T>
std::vector<std::vector<T> > GeneralizedCartesianProduct(std::vector<std::vector<T> > const & x){
  // Input: 
  // - x which is a [[...] (/*with k_1 elements*/), 
  // ..., [...] (/*with k_n elements*/)]
  
  // ans_size can get really large
  // at most O(n^n)
  // so be careful with 
  // possible overflow problems
  unsigned ans_size = 1;
  for(auto const & entry : x)
    ans_size *= entry.size();

  std::vector<std::vector<T> > ans(ans_size, std::vector<T>(0));
  if(ans_size){
    unsigned max_repetition = 1;
    for(auto const & entry : x){
      // Invariant: at the i-th iteration
      // of this loop, we have k_{i+1} ... k_n copies
      // of GeneralizedCartesianProduct([[]_1, ..., []_i])
      // stored in ans
      unsigned index = 0;
      while(index < ans_size)
        for(auto const & value : entry){
          unsigned index_repetition = 0;
          while(index_repetition++ < max_repetition)
            ans[index++].push_back(value);
        }
      max_repetition *= entry.size();
    }
  }

  return ans;
}

template<typename T>
void printGeneralizedCartesianProduct(std::vector<std::vector<T> > const & x){
  for(auto const & entry : x){
    for(auto const & value : entry)
      std::cout << value << " ";
    std::cout << std::endl;
  }
}
#endif

