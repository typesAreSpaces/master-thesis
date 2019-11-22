#include "Purifier.h"

Purifier::Purifier(z3::expr & e, const std::vector<std::string> & symbols_to_elim){
  // TODO: Keep working here
}

Purifier::~Purifier(){
}

z3::expr Purifier::getEUFFormula(){
  return this->euf_formula;
}

z3::expr Purifier::getOctagonFormula(){
  return this->octagon_formula;
}
