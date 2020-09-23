#include <fstream>
#include <iostream>
#include <string>
#define IZ3_PREFIX     "iz3_instance_"
#define MATHSAT_PREFIX "mathsat_instance_"
#define EUFI_PREFIX    "eufi_instance_"
#define SUFFIX         ".smt2"

// A-part : f^n(x) = f^{n+1}(x), f^2(x) = x, f(a) \neq a
// B-part : x = a

void iz3_instance(unsigned);
void mathsat_instance(unsigned);
void eufi_instance(unsigned);

int main(){

  //unsigned n = 10000;
  unsigned n = 10;

  iz3_instance(n);
  system(("time ../../bin/z3-interp  " + (IZ3_PREFIX + std::to_string(n)) + SUFFIX).c_str());
  system(("rm " + (IZ3_PREFIX + std::to_string(n)) + SUFFIX).c_str());

  mathsat_instance(n);
  system(("time ../../bin/mathsat " + (MATHSAT_PREFIX + std::to_string(n)) + SUFFIX).c_str());
  system(("rm " + (MATHSAT_PREFIX + std::to_string(n)) + SUFFIX).c_str());

  eufi_instance(n);
  system(("time ./bin/eufi " + (EUFI_PREFIX + std::to_string(n)) + SUFFIX).c_str());
  system(("rm " + (EUFI_PREFIX + std::to_string(n)) + SUFFIX).c_str());
  
  return 0;
}

void iz3_instance(unsigned n){
  std::ofstream out(IZ3_PREFIX + std::to_string(n) + SUFFIX);

  out << "(set-option :produce-interpolants true)" << std::endl;
  out << "(declare-sort A 0)" << std::endl;
  out << "(declare-fun x () A)" << std::endl;
  out << "(declare-fun a () A)" << std::endl;
  out << "(declare-fun f (A) A)" << std::endl;
  out << std::endl;
  out << "(assert (!" << std::endl;
  out << "(and" << std::endl;
  // ------------------------------------------------------------
  // Instantiation
  out << "(= "; 
  for(unsigned i = 0; i < n; ++i)
    out << "(f ";
  out << "x";
  for(unsigned i = 0; i < n; ++i)
    out << ")";
  out << " ";
  n++;
  for(unsigned i = 0; i < n; ++i)
    out << "(f ";
  out << "x";
  for(unsigned i = 0; i < n; ++i)
    out << ")";
  out << ") ;; Parametrized formula for n = " << --n << std::endl;
  // ------------------------------------------------------------
  out << "(= (f (f x)) x)" << std::endl;
  out << "(distinct (f a) a)" << std::endl;
  out << ") :named a_part" << std::endl;
  out << "))" << std::endl;
  out << std::endl;
  out << "(assert (!" << std::endl;
  out << "(= x a)" << std::endl;
  out << ":named b_part" << std::endl;
  out << "))" << std::endl;
  out << std::endl;
  out << "(check-sat)" << std::endl;
  out << "(get-interpolant a_part b_part)" << std::endl;
  out.close();
} 

void mathsat_instance(unsigned n){
  std::ofstream out(MATHSAT_PREFIX + std::to_string(n) + SUFFIX);

  out << "(set-option :produce-interpolants true)" << std::endl;
  out << "(declare-sort A 0)" << std::endl;
  out << "(declare-fun x () A)" << std::endl;
  out << "(declare-fun a () A)" << std::endl;
  out << "(declare-fun f (A) A)" << std::endl;
  out << std::endl;
  out << "(assert (!" << std::endl;
  out << "(and" << std::endl;
  // ------------------------------------------------------------
  // Instantiation
  out << "(= "; 
  for(unsigned i = 0; i < n; ++i)
    out << "(f ";
  out << "x";
  for(unsigned i = 0; i < n; ++i)
    out << ")";
  out << " ";
  n++;
  for(unsigned i = 0; i < n; ++i)
    out << "(f ";
  out << "x";
  for(unsigned i = 0; i < n; ++i)
    out << ")";
  out << ") ;; Parametrized formula for n = " << --n << std::endl;
  // ------------------------------------------------------------
  out << "(= (f (f x)) x)" << std::endl;
  out << "(distinct (f a) a)" << std::endl;
  out << ") :interpolation-group a_part" << std::endl;
  out << "))" << std::endl;
  out << std::endl;
  out << "(assert (!" << std::endl;
  out << "(= x a)" << std::endl;
  out << ":interpolation-group b_part" << std::endl;
  out << "))" << std::endl;
  out << std::endl;
  out << "(check-sat)" << std::endl;
  out << "(get-interpolant (a_part))" << std::endl;
  out << "(exit)" << std::endl;
  out.close();
}

void eufi_instance(unsigned n){
  std::ofstream out(EUFI_PREFIX + std::to_string(n) + SUFFIX);

  out << "(declare-sort A 0)" << std::endl;
  out << "(declare-fun x () A)" << std::endl;
  out << "(declare-fun a () A)" << std::endl;
  out << "(declare-fun f (A) A)" << std::endl;
  out << std::endl;
  out << "(assert (and" << std::endl;
  // ------------------------------------------------------------
  // Instantiation
  out << "(= "; 
  for(unsigned i = 0; i < n; ++i)
    out << "(f ";
  out << "x";
  for(unsigned i = 0; i < n; ++i)
    out << ")";
  out << " ";
  n++;
  for(unsigned i = 0; i < n; ++i)
    out << "(f ";
  out << "x";
  for(unsigned i = 0; i < n; ++i)
    out << ")";
  out << ") ;; Parametrized formula for n = " << --n << std::endl;
  // ------------------------------------------------------------
  out << "(= (f (f x)) x)" << std::endl;
  out << "(distinct (f a) a)" << std::endl;
  out << "))" << std::endl;
  out << std::endl;
  out << "(assert (and" << std::endl;
  out << "(= x a)" << std::endl;
  out << "))" << std::endl;
  out << std::endl;
  out << "(check-sat)" << std::endl;
  out.close();
}
