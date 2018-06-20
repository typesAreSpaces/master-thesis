#include "terms.hpp"

typedef std::vector<Term *> Terms;

int Term::objectCount = 0;

void Term::setName(std::string x){
  name = x;
}

std::string Term::getName(){
  return name;
}

void Term::setId(int x){
  id = x;
}

int Term::getId(){
  return id;
}

std::ostream & operator<<(std::ostream & out, Term & obj) {
  return obj.print(&out);
}

Variable::Variable(std::string x){
  setName(x);
  setId(objectCount);
  objectCount++;
}

std::ostream & Variable::print(std::ostream * out){
  *out <<  "Variable " << getName();
  return *out;
}

Constant::Constant(std::string x){
  setName(x);
  setId(objectCount);
  objectCount++;
}

std::ostream & Constant::print(std::ostream * out){
  *out << "Constant " << getName();
  return *out;
}

Function::Function(std::string x){
  setName(x);
  setId(objectCount);
  objectCount++;
}

std::ostream & Function::print(std::ostream * out){
  *out << "Function " << getName() << "(";
  Terms * temp = getArgs();
  int i = 0;
  for(Terms::iterator it = temp->begin();
      it != temp->end();
      ++it){
    if(i != 0)
      *out << ", ";
    (*it)->print(out);
    ++i;
  }
  *out << ")";
  return *out;
}

void Function::addArg(Term * x){
  args.push_back(x); 
}

Terms * Function::getArgs(){
  return &args;
}
