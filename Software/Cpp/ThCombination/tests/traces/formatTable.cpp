#include <iostream>
#include <fstream>
#include <string>
#include <vector>

int main(){
  std::ifstream input("extensive.txt");
  std::string line;
  unsigned limit = 100;
  unsigned count = 0;
  unsigned id_case = 0;
  std::vector<unsigned> results({});

  while(getline(input, line)){
    if(count++ % 2){
      results.push_back(std::stoul(line));
      id_case++;
    }
    if(id_case == limit)
      break;
  }

  for(unsigned i = 0; i < limit/5; ++i)
    std::cout 
      << "\\#" << i+1 << " & " << results[i] << " & "
      << "\\#" << i+21 << " & "<< results[i + 20] << " & "
      << "\\#" << i+41 << " & "<< results[i + 40] << " & "
      << "\\#" << i+61 << " & " << results[i + 60] << " & "
      << "\\#" << i+81 << " & " << results[i + 80] << " \\\\"
      << std::endl;

  return 0;
}
