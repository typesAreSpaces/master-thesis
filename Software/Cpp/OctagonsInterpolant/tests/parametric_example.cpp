#include <exception>
#include <thread>
#include <fstream>
#include <iostream>
#include <string>
#define IZ3_PREFIX     "iz3_instance_"
#define MATHSAT_PREFIX "mathsat_instance_"
#define EUFI_PREFIX    "octi_instance_"
#define SMT_SUFFIX     ".smt2"
#define TXT_SUFFIX     ".txt"

// A-part : x_2 + x_2 <= 1, ..., x_{i+1} - x_i <= 1, x_1 - x_n <= 1, 
// B-part : x_1 > \floor{n/2}

void iz3_instance(unsigned);
void mathsat_instance(unsigned);
void octi_instance(unsigned);

void iz3_process(unsigned);
void mathsat_process(unsigned);
void octi_process_0(unsigned);
void octi_process_1(unsigned);
void octi_process_2(unsigned);
void octi_process_3(unsigned);
void octi_process_4(unsigned);
void octi_process_5(unsigned);
void octi_process_6(unsigned);

int main(){

  unsigned n = 10000;
  //unsigned n = 100;
  //unsigned n = 10;

#if 1
  std::thread iz3(iz3_process, n);
  std::thread mathsat(mathsat_process, n);
  //std::thread octi_0(octi_process_0, n);
  //std::thread octi_1(octi_process_1, n);
  //std::thread octi_2(octi_process_2, n);
  //std::thread octi_3(octi_process_3, n);
  //std::thread octi_4(octi_process_4, n);
  //std::thread octi_5(octi_process_5, n);
  //std::thread octi_6(octi_process_6, n);
  
  iz3.join();
  mathsat.join();
  //octi_0.join();
  //octi_1.join();
  //octi_2.join();
  //octi_3.join();
  //octi_4.join();
  //octi_5.join();
  //octi_6.join();
#endif 

  return 0;
}

void iz3_instance(unsigned n){
  std::ofstream out(IZ3_PREFIX + std::to_string(n) + SMT_SUFFIX);

  out << "(set-option :produce-interpolants true)" << std::endl;
  // ------------------------------------------------------------
  for(unsigned i = 1; i <= n; ++i)
    out << "(declare-fun x" << i << " () Int)" << std::endl;
  // ------------------------------------------------------------
  out << std::endl;
  out << "(assert (!" << std::endl;
  out << "(and" << std::endl;
  out << "(<= (+ x1 x2) 1)" << std::endl;
  // ------------------------------------------------------------
  for(unsigned i = 2; i < n; ++i)
    out << "(<= (- x" << (i+1) << " x" << i << ") 1)" << std::endl;
  out << "(<= (- x1 x" << n << ") 1)" << std::endl;
  // ------------------------------------------------------------
  out << ") :named a_part" << std::endl;
  out << "))" << std::endl;
  out << std::endl;
  out << "(assert (!" << std::endl;
  out << "(> x1 " << n/2 << ")" << std::endl;
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
  // ------------------------------------------------------------
  for(unsigned i = 1; i <= n; ++i)
    out << "(declare-fun x" << i << " () Int)" << std::endl;
  // ------------------------------------------------------------
  out << std::endl;
  out << "(assert (!" << std::endl;
  out << "(and" << std::endl;
  out << "(<= (+ x1 x2) 1)" << std::endl;
  // ------------------------------------------------------------
  // Instantiation
  for(unsigned i = 2; i < n; ++i)
    out << "(<= (- x" << (i+1) << " x" << i << ") 1)" << std::endl;
  out << "(<= (- x1 x" << n << ") 1)" << std::endl;
  // ------------------------------------------------------------
  // ------------------------------------------------------------
  out << ") :interpolation-group a_part" << std::endl;
  out << "))" << std::endl;
  out << std::endl;
  out << "(assert (!" << std::endl;
  out << "(> x1 " << n/2 << ")" << std::endl;
  out << ":interpolation-group b_part" << std::endl;
  out << "))" << std::endl;
  out << std::endl;
  out << "(check-sat)" << std::endl;
  out << "(get-interpolant (a_part))" << std::endl;
  out << "(exit)" << std::endl;
  out.close();
}

void octi_instance(unsigned n){
  std::ofstream out(EUFI_PREFIX + std::to_string(n) + SMT_SUFFIX);

  out << std::endl;
  // ------------------------------------------------------------
  for(unsigned i = 1; i <= n; ++i)
    out << "(declare-fun x" << i << " () Int)" << std::endl;
  // ------------------------------------------------------------
  out << "(assert (and" << std::endl;
  out << "(<= (+ x1 x2) 1)" << std::endl;
  // ------------------------------------------------------------
  // Instantiation
  for(unsigned i = 2; i < n; ++i)
    out << "(<= (- x" << (i+1) << " x" << i << ") 1)" << std::endl;
  out << "(<= (- x1 x" << n << ") 1)" << std::endl;
  // ------------------------------------------------------------
  out << "))" << std::endl;
  out << std::endl;
  out << "(assert (and" << std::endl;
  out << "(> x1 " << n/2 << ")" << std::endl;
  out << "))" << std::endl;
  out << std::endl;
  out << "(check-sat)" << std::endl;
  out.close();
}

void iz3_process(unsigned n){
  system("rm -rf iz3_results.txt");
  for(unsigned i = 1; i < n; ++i){
    iz3_instance(i);
    system(("echo \"test: " + std::to_string(i) + "\">> iz3_results.txt").c_str());
    system(("{ time ../../bin/z3-interp  " + (IZ3_PREFIX + std::to_string(i)) + SMT_SUFFIX + "; } 2>> iz3_results.txt").c_str());
    system(("rm " + (IZ3_PREFIX + std::to_string(i)) + SMT_SUFFIX).c_str());
  }
}

void mathsat_process(unsigned n){
  system("rm -rf mathsat_results.txt");
  for(unsigned i = 1; i < n; ++i){
    mathsat_instance(i);
    system(("echo \"test: " + std::to_string(i) + "\">> mathsat_results.txt").c_str());
    system(("{ time ../../bin/mathsat " + (MATHSAT_PREFIX + std::to_string(i)) + SMT_SUFFIX + "; } 2>> mathsat_results.txt").c_str());
    system(("rm " + (MATHSAT_PREFIX + std::to_string(i)) + SMT_SUFFIX).c_str());
  }
}

void octi_process_0(unsigned n){
  system("rm -rf octi_results_0.txt");
  for(unsigned i = 6000; i < n; ++i){
    unsigned r = i % 18;
    if(r == 0){
      octi_instance(i);
      system(("echo \"test: " + std::to_string(i) + "\">> octi_results_0.txt").c_str());
      system(("{ time ./bin/octi " + (EUFI_PREFIX + std::to_string(i)) + SMT_SUFFIX + "; } 2>> octi_results_0.txt").c_str());
      system(("rm " + (EUFI_PREFIX + std::to_string(i)) + SMT_SUFFIX).c_str());
    }
  }
}

void octi_process_1(unsigned n){
  system("rm -rf octi_results_1.txt");
  for(unsigned i = 6000; i < n; ++i){
    unsigned r = i % 18;
    if(r == 1){
      octi_instance(i);
      system(("echo \"test: " + std::to_string(i) + "\">> octi_results_1.txt").c_str());
      system(("{ time ./bin/octi " + (EUFI_PREFIX + std::to_string(i)) + SMT_SUFFIX + "; } 2>> octi_results_1.txt").c_str());
      system(("rm " + (EUFI_PREFIX + std::to_string(i)) + SMT_SUFFIX).c_str());
    }
  }
}

void octi_process_2(unsigned n){
  system("rm -rf octi_results_2.txt");
  for(unsigned i = 6000; i < n; ++i){
    unsigned r = i % 18;
    if(r == 2){
      octi_instance(i);
      system(("echo \"test: " + std::to_string(i) + "\">> octi_results_2.txt").c_str());
      system(("{ time ./bin/octi " + (EUFI_PREFIX + std::to_string(i)) + SMT_SUFFIX + "; } 2>> octi_results_2.txt").c_str());
      system(("rm " + (EUFI_PREFIX + std::to_string(i)) + SMT_SUFFIX).c_str());
    }
  }
}

void octi_process_3(unsigned n){
  system("rm -rf octi_results_3.txt");
  for(unsigned i = 6000; i < n; ++i){
    unsigned r = i % 18;
    if(r == 3){
      octi_instance(i);
      system(("echo \"test: " + std::to_string(i) + "\">> octi_results_3.txt").c_str());
      system(("{ time ./bin/octi " + (EUFI_PREFIX + std::to_string(i)) + SMT_SUFFIX + "; } 2>> octi_results_3.txt").c_str());
      system(("rm " + (EUFI_PREFIX + std::to_string(i)) + SMT_SUFFIX).c_str());
    }
  }
}

void octi_process_4(unsigned n){
  system("rm -rf octi_results_4.txt");
  for(unsigned i = 6000; i < n; ++i){
    unsigned r = i % 18;
    if(r == 4){
      octi_instance(i);
      system(("echo \"test: " + std::to_string(i) + "\">> octi_results_4.txt").c_str());
      system(("{ time ./bin/octi " + (EUFI_PREFIX + std::to_string(i)) + SMT_SUFFIX + "; } 2>> octi_results_4.txt").c_str());
      system(("rm " + (EUFI_PREFIX + std::to_string(i)) + SMT_SUFFIX).c_str());
    }
  }
}

void octi_process_5(unsigned n){
  system("rm -rf octi_results_5.txt");
  for(unsigned i = 6000; i < n; ++i){
    unsigned r = i % 18;
    if(r == 5){
      octi_instance(i);
      system(("echo \"test: " + std::to_string(i) + "\">> octi_results_5.txt").c_str());
      system(("{ time ./bin/octi " + (EUFI_PREFIX + std::to_string(i)) + SMT_SUFFIX + "; } 2>> octi_results_5.txt").c_str());
      system(("rm " + (EUFI_PREFIX + std::to_string(i)) + SMT_SUFFIX).c_str());
    }
  }
}

void octi_process_6(unsigned n){
  system("rm -rf octi_results_6.txt");
  for(unsigned i = 6000; i < n; ++i){
    unsigned r = i % 18;
    if(r == 6){
      octi_instance(i);
      system(("echo \"test: " + std::to_string(i) + "\">> octi_results_6.txt").c_str());
      system(("{ time ./bin/octi " + (EUFI_PREFIX + std::to_string(i)) + SMT_SUFFIX + "; } 2>> octi_results_6.txt").c_str());
      system(("rm " + (EUFI_PREFIX + std::to_string(i)) + SMT_SUFFIX).c_str());
    }
  }
}

