#ifndef _VERTEX_
#define _VERTEX_

#include <iostream>
#include <vector>
#include <cassert>
#include "CircularList.h"

class Term{
 private:
  static unsigned        total_num_vertex;
  std::string            name;
  bool                   is_symbol_common;
  bool                   defined;
  unsigned               id, arity;
  std::vector<Term*>     successors;
  CircularList<unsigned> predecessors;
  
  void addPredecessor(unsigned);

 public:
  Term(std::string, unsigned);
  Term();
  ~Term();

  void setName(std::string);
  void setSymbolCommonQ(bool);
  void define();
  void setArity(unsigned);
  void addSuccessor(Term *);
  void mergePredecessors(Term *);x
x  
  static unsigned getTotalNumTerm();
  const std::string & getName();
  bool getSymbolCommonQ();
  unsigned getId();
  unsigned getArity();
  unsigned getLength();
  const std::vector<Term*> & getSuccessors();
  CircularList<unsigned> & getPredecessors();
  std::string to_string();
  Term * getLeftChild();
  Term * getRightChild();
  
  std::ostream & functionPrettyPrint (std::ostream &);
  friend std::ostream & operator << (std::ostream &, Term &);
  friend bool operator ==(const Term &, const Term &);
  friend bool operator !=(const Term &, const Term &);
  friend bool operator <(const Term &, const Term &);
  friend bool operator <=(const Term &, const Term &);
  friend bool operator >(const Term &, const Term &);
  friend bool operator >=(const Term &, const Term &);
};

#endif
