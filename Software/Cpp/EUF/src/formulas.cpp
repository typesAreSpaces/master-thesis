#include "formulas.hpp"


void Formula::setName(std::string x){
  name = x;
}

std::string Formula::getName(){
  return name;
}

void Formula::setAntecedent(Term * x, Term * y, bool isEqual){
  antecedent = std::make_pair(std::make_pair(x, y), isEqual);
}

atomicFormula Formula::getAntecedent(){
  return antecedent;
}

Eq::Eq(std::string name, Term * x, Term * y, bool isEqual){
  setName(name);
  setAntecedent(x, y, isEqual);
}

std::ostream & Eq::print(std::ostream * out){
  *out << "Equation " << getName() << endl;
  return *out;
}

std::ostream & HornClause::print(std::ostream * out){
  *out << "Function " << getName();
  return *out;
}
