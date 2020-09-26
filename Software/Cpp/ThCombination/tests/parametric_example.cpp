#include <exception>
#include <thread>
#include <fstream>
#include <iostream>
#include <string>
#define IZ3_PREFIX     "iz3_instance_"
#define MATHSAT_PREFIX "mathsat_instance_"
#define THCI_PREFIX    "thci_instance_"
#define SMT_SUFFIX     ".smt2"
#define TXT_SUFFIX     ".txt"

// A-part : 1 <= x, x <= n
// B-part : f(x) == a, f(1) \neq a, \dots, f(n) \neq a

void iz3_instance(unsigned);
void mathsat_instance(unsigned);
void thci_instance(unsigned);

void iz3_process(unsigned);
void mathsat_process(unsigned);
void thci_process_0(unsigned);
void thci_process_1(unsigned);
void thci_process_2(unsigned);
void thci_process_3(unsigned);

int main(){

  unsigned n = 8;

  std::thread iz3(iz3_process, n);
  std::thread mathsat(mathsat_process, n);
  std::thread thci_0(thci_process_0, n);
  std::thread thci_1(thci_process_1, n);
  std::thread thci_2(thci_process_2, n);
  std::thread thci_3(thci_process_3, n);
  
  iz3.join();
  mathsat.join();
  thci_0.join();
  thci_1.join();
  thci_2.join();
  thci_3.join();

  return 0;
}

void iz3_instance(unsigned n){
  std::ofstream out(IZ3_PREFIX + std::to_string(n) + SMT_SUFFIX);

  out << "(set-option :produce-interpolants true)" << std::endl;
  out << "(declare-fun x () Int)" << std::endl;
  out << "(declare-fun a () Int)" << std::endl;
  out << "(declare-fun f (Int) Int)" << std::endl;
  out << std::endl;
  out << "(assert (!" << std::endl;
  out << "(and" << std::endl;
  out << "(<= 1 x)" << std::endl;
  out << "(<= x " << n << ")" << std::endl;
  out << ") :named a_part" << std::endl;
  out << "))" << std::endl;
  out << std::endl;
  out << "(assert (!" << std::endl;
  out << "(and" << std::endl;
  out << "(= (f x) a)" << std::endl;
  for(unsigned i = 1; i <= n; ++i)
    out << "(distinct (f " << i << ") a)" << std::endl;
  out << ")" << std::endl;
  out << ":named b_part" << std::endl;
  out << "))" << std::endl;
  out << std::endl;
  out << "(check-sat)" << std::endl;
  out << "(get-interpolant a_part b_part)" << std::endl;
  out.close();
} 

void mathsat_instance(unsigned n){
  std::ofstream out(MATHSAT_PREFIX + std::to_string(n) + SMT_SUFFIX);

  out << "(set-option :produce-interpolants true)" << std::endl;
  out << "(declare-fun x () Int)" << std::endl;
  out << "(declare-fun a () Int)" << std::endl;
  out << "(declare-fun f (Int) Int)" << std::endl;
  out << std::endl;
  out << "(assert (!" << std::endl;
  out << "(and" << std::endl;
  out << "(<= 1 x)" << std::endl;
  out << "(<= x " << n << ")" << std::endl;
  out << ") :interpolation-group a_part" << std::endl;
  out << "))" << std::endl;
  out << std::endl;
  out << "(assert (!" << std::endl;
  out << "(and" << std::endl;
  out << "(= (f x) a)" << std::endl;
  for(unsigned i = 1; i <= n; ++i)
    out << "(distinct (f " << i << ") a)" << std::endl;
  out << ")" << std::endl;
  out << ":interpolation-group b_part" << std::endl;
  out << "))" << std::endl;
  out << std::endl;
  out << "(check-sat)" << std::endl;
  out << "(get-interpolant (a_part))" << std::endl;
  out << "(exit)" << std::endl;
  out.close();
}

void thci_instance(unsigned n){
  std::ofstream out(THCI_PREFIX + std::to_string(n) + SMT_SUFFIX);

  out << "(declare-fun x () Int)" << std::endl;
  out << "(declare-fun a () Int)" << std::endl;
  out << "(declare-fun f (Int) Int)" << std::endl;
  out << std::endl;
  out << "(assert (and" << std::endl;
  out << "(<= 1 x)" << std::endl;
  out << "(<= x " << n << ")" << std::endl;
  out << "))" << std::endl;
  out << std::endl;
  out << "(assert (and" << std::endl;
  out << "(= (f x) a)" << std::endl;
  for(unsigned i = 1; i <= n; ++i)
    out << "(distinct (f " << i << ") a)" << std::endl;
  out << "))" << std::endl;
  out << std::endl;
  out << "(check-sat)" << std::endl;
  out.close();
}

void iz3_process(unsigned n){
  system("rm -rf iz3_results.txt");
  for(unsigned i = 2; i < n; ++i){
    iz3_instance(i);
    system(("echo \"test: " + std::to_string(i) + "\">> iz3_results.txt").c_str());
    system(("{ time ../../bin/z3-interp  " + (IZ3_PREFIX + std::to_string(i)) + SMT_SUFFIX + "; } 2>> iz3_results.txt").c_str());
    system(("rm " + (IZ3_PREFIX + std::to_string(i)) + SMT_SUFFIX).c_str());
  }
}

void mathsat_process(unsigned n){
  system("rm -rf mathsat_results.txt");
  for(unsigned i = 2; i < n; ++i){
    mathsat_instance(i);
    system(("echo \"test: " + std::to_string(i) + "\">> mathsat_results.txt").c_str());
    system(("{ time ../../bin/mathsat " + (MATHSAT_PREFIX + std::to_string(i)) + SMT_SUFFIX + "; } 2>> mathsat_results.txt").c_str());
    system(("rm " + (MATHSAT_PREFIX + std::to_string(i)) + SMT_SUFFIX).c_str());
  }
}

void thci_process_0(unsigned n){
  system("rm -rf thci_results_0.txt");
  for(unsigned i = 2; i < n; ++i){
    unsigned r = i % 3;
    if(r == 0){
      thci_instance(i);
      system(("echo \"test: " + std::to_string(i) + "\">> thci_results_0.txt").c_str());
      system(("{ time ./bin/thci " + (THCI_PREFIX + std::to_string(i)) + SMT_SUFFIX + "; } 2>> thci_results_0.txt").c_str());
      system(("rm " + (THCI_PREFIX + std::to_string(i)) + SMT_SUFFIX).c_str());
    }
  }
}

void thci_process_1(unsigned n){
  system("rm -rf thci_results_1.txt");
  for(unsigned i = 2; i < n; ++i){
    unsigned r = i % 3;
    if(r == 1){
      thci_instance(i);
      system(("echo \"test: " + std::to_string(i) + "\">> thci_results_1.txt").c_str());
      system(("{ time ./bin/thci " + (THCI_PREFIX + std::to_string(i)) + SMT_SUFFIX + "; } 2>> thci_results_1.txt").c_str());
      system(("rm " + (THCI_PREFIX + std::to_string(i)) + SMT_SUFFIX).c_str());
    }
  }
}

void thci_process_2(unsigned n){
  system("rm -rf thci_results_2.txt");
  for(unsigned i = 2; i < n; ++i){
    unsigned r = i % 3;
    if(r == 2){
      thci_instance(i);
      system(("echo \"test: " + std::to_string(i) + "\">> thci_results_2.txt").c_str());
      system(("{ time ./bin/thci " + (THCI_PREFIX + std::to_string(i)) + SMT_SUFFIX + "; } 2>> thci_results_2.txt").c_str());
      system(("rm " + (THCI_PREFIX + std::to_string(i)) + SMT_SUFFIX).c_str());
    }
  }
}
