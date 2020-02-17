#ifndef _VERTEX_
#define _VERTEX_

#include <vector>
#include <cassert>
#include "CircularList.h"

class Term {

  std::string         name;
  bool                is_symbol_common;
  bool                is_defined;
  // A term is `defined` when we specify
  // its successors and predecessors
  unsigned            id, arity, original_arity;
  std::vector<Term*>  successors, original_successors;
  CircularList<Term*> predecessors;
  
public:
  Term(std::string, unsigned, unsigned);
  Term();
  ~Term();

  void setName(std::string);
  void setSymbolCommonQ(bool);
  void define();
  void setArity(unsigned, unsigned);
  void addSuccessor(Term *);
  void addOriginalSuccessor(Term *);
  void mergePredecessors(Term *);

  static unsigned            total_num_vertex;
  static unsigned            getTotalNumTerm();
  const std::string &        getName();
  bool                       getSymbolCommonQ();
  unsigned                   getId();
  unsigned                   getArity();
  unsigned                   getOriginalArity();
  unsigned                   getLength();
  const std::vector<Term*> & getSuccessors();
  const std::vector<Term*> & getOriginalSuccessors();
  CircularList<Term*> &      getPredecessors();
  std::string                to_string();
  Term *                     getLeftChild();
  Term *                     getRightChild();
  std::ostream &             functionPrettyPrint (std::ostream &);
  friend std::ostream &      operator << (std::ostream &, Term &);
  friend bool                operator ==(const Term &, const Term &);
  friend bool                operator !=(const Term &, const Term &);
  friend bool                operator <(const Term &, const Term &);
  friend bool                operator <=(const Term &, const Term &);
  friend bool                operator >(const Term &, const Term &);
  friend bool                operator >=(const Term &, const Term &);
};

#endif
