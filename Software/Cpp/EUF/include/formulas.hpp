#ifndef _FORMS_
#define _FORMS_

#include <utility>
#include <vector>
#include <iostream>
#include "terms.hpp"

typedef std::pair< std::pair<Term *, Term * >, bool > atomicFormula;

class Formula{
private:
  std::string name;
  atomicFormula antecedent;
public:
  void setName(std::string);
  std::string getName();
  
  void setAntecedent(Term *, Term *, bool);
  atomicFormula getAntecedent();
  virtual std::ostream & print(std::ostream *) = 0;
  friend std::ostream & operator<<(std::ostream &, Formula &);
};

class Eq : public Formula{
public:
  Eq(std::string, Term *, Term *, bool);
  
  std::ostream & print(std::ostream *);
};

class HornClause : public Formula{
private:
  std::vector<atomicFormula*> consequents;
public:
  // TODO
  // ? HornClause();
  
  void addConsequent(atomicFormula *);
  std::vector<atomicFormula> * getConsequents();
  
  std::ostream & print(std::ostream *);
};

#endif
