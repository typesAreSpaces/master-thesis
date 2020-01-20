#include <iostream>
#include <fstream>
#include <set>
#include <map>
#include <string>

int main(int argc, char ** argv){
  
  std::string input_info(argv[1]);
  std::ifstream file(input_info);
	
  std::string input;
  int i;
  double j;
  std::map<int, double> m;
  std::map<int, int> count;
  std::set<int> s;

  while(!file.eof()){
    file >> input;
    i = stoi(input.substr(0, input.find(",")));
    j = stod(input.substr(input.find(",") + 1));
    if(s.find(i) == s.end()){
      s.insert(i);
      m[i] = j;
      count[i] = 1;
    }
    else{
      m[i] += j;
      ++count[i];
    }
  }

  for(std::map<int, int>::iterator it = count.begin(); it != count.end(); ++it)
    std::cout << it->first << "," << m[it->first]/(double)count[it->first] << std::endl;
  
  return 0;
}
