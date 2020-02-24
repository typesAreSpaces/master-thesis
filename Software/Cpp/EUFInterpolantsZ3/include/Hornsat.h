#ifndef _HORNSAT_
#define _HORNSAT_
#define FALSELITERAL 0

#include <iostream>
#include <queue>
#include <vector>
#include "HornClauses.h"

struct Clause {
  unsigned clause_id;
  struct Clause * next;
  Clause(unsigned id, struct Clause * clause) : clause_id(id), next(clause){}
  struct Clause * add(unsigned element){
    return new Clause(element, this);
  }
  class iterator {
    struct Clause * it;
  public:
    iterator(struct Clause * n) : it(n){}
    bool operator ==(iterator const & other){
      return it == other.it;
    }
    bool operator !=(iterator const & other){
      return it != other.it;
    }
    iterator & operator ++(){
      it = it->next;
      return *this;
    }
    struct Clause * operator *(){
      return it;
    }
  };
  iterator begin(){
    return iterator(this);
  }
  iterator end(){
    return iterator(nullptr);
  }
};

struct Literal {
  static unsigned curr_num_literals;
  unsigned literal_id;
  unsigned l_id, r_id;
  unsigned l_class, r_class;
  bool val;
  struct Clause * clause_list;
  
  Literal(unsigned literal_id, bool val, struct Clause * clause_list) :
  literal_id(literal_id), l_id(0), r_id(0), l_class(0), r_class(0),
    val(val), clause_list(clause_list){}
  Literal() : Literal(curr_num_literals++, false, nullptr) {}
  friend std::ostream & operator << (std::ostream & os, const Literal & l){
    os << "Literal: " << l.literal_id
       << " Equation: " << l.l_id << "=" << l.r_id << " (" << l.l_class << "=" << l.r_class << ")"
       << " Val: " << l.val;
    return os;
  }
};

enum EquationSide { LHS, RHS };

struct ClassListPos {
  Literal * lit_pointer;
  EquationSide eq_side;
  ClassListPos(Literal * lit_pointer, EquationSide eq_side) :
    lit_pointer(lit_pointer), eq_side(eq_side){}
  friend std::ostream & operator << (std::ostream & os, const ClassListPos & clp){
    os << *(clp.lit_pointer) << (clp.eq_side == LHS ? " LHS" : " RHS");
    return os;
  }
};

class Hornsat {
  bool consistent;
  unsigned num_pos;
  std::vector<Literal> list_of_literals;
  std::vector<std::vector<ClassListPos> > class_list;
  std::queue<unsigned> facts;
  std::vector<unsigned> num_args, pos_lit_list;

  void unionupdate(UnionFind &, unsigned, unsigned);
  
 public:
  Hornsat(std::istream &);
  Hornsat(const HornClauses &, UnionFind &);
  ~Hornsat();
  void satisfiable();
  void satisfiable(UnionFind &);
  bool isConsistent();
  friend std::ostream & operator << (std::ostream &, const Hornsat &);
};

#endif
