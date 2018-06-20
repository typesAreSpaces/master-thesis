#ifndef _TERMS_
#define _TERMS_

#include <vector>
#include <string>
#include <iostream>

class Term{
private:
  int id;
  std::string name;
public:
  static int objectCount;

  void setName(std::string);
  std::string getName();

  void setId(int);
  int getId();

  virtual std::ostream & print (std::ostream *) = 0;
  friend std::ostream & operator<<(std::ostream &, Term &);
};

class Variable : public Term{
public:
  Variable(std::string);
  std::ostream & print(std::ostream *);
};

class Constant : public Term{
public:
  Constant(std::string);
  std::ostream & print(std::ostream *);
};

class Function : public Term{
private:
  std::vector<Term *> args;
public:
  Function(std::string);
  std::ostream & print(std::ostream *);

  void addArg(Term *);
  std::vector<Term*> * getArgs();
};

#endif
