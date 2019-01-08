#include <iostream>
#include <fstream>
#include <cstdlib>
using namespace std;

int main(int argc, char ** argv){
	if(argc > 1){
		std::string address_path(argv[1]);
		std::string command = "mkdir " + address_path,
			command_rm, command_touch, name;
		std::ofstream f;
		std::system(command.c_str());
		for(int i = 10; i < 10000000; i*=10){
			name = address_path + "/test_" + std::to_string(i) + ".txt";
			command_rm = "rm -rf " + name;
			command_touch = "touch " + name;
			system(command_rm.c_str());
			system(command_touch.c_str());
			f.open(name);
			f << i << "\n";
			f << "x 0\n";
			f << "g 2 0 0\n";
			for(int j = 2; j < i; ++j)
				f << "g 2 " << rand() % j << " " << rand() % j << "\n";
			f << "1\n0 1\n";
			f.close();
		}
	}
}
