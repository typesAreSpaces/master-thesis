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
    struct Clause * r = new Clause(element, this);
    return r;
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
  unsigned lclass, rclass;
  bool val;
  struct Clause * clause_list;
  
  Literal(unsigned literal_id, bool val, struct Clause * clause_list) :
  literal_id(literal_id), l_id(0), r_id(0), lclass(0), rclass(0),
    val(val), clause_list(clause_list){}
  Literal() : Literal(curr_num_literals++, false, nullptr) {}
  static void print(){
    std::cout << "current number of literals " << curr_num_literals << std::endl; 
  }
};

enum EquationSide { LHS, RHS };

struct ClassListPos {
  Literal * lit_pointer;
  EquationSide eq_pos;
  ClassListPos(Literal * lit_pointer, EquationSide eq_pos) :
    lit_pointer(lit_pointer), eq_pos(eq_pos){}
  friend std::ostream & operator << (std::ostream & os, const ClassListPos & clp){
    os << clp.lit_pointer->literal_id << (clp.eq_pos == LHS ? " LHS" : " RHS");
    return os;
  }
};

class Hornsat {
  bool consistent;
  unsigned num_pos;
  std::vector<Literal> list_of_literals;
  std::vector<std::vector<ClassListPos> > classlist;
  std::queue<unsigned> facts;
  std::vector<unsigned> num_args, pos_lit_list;

  void unionupdate(UnionFind &, unsigned, unsigned);
  
 public:
  Hornsat(std::istream &);
  Hornsat(const HornClauses &);
  ~Hornsat();
  void satisfiable();
  void satisfiable(UnionFind &);
  bool isConsistent();
  friend std::ostream & operator << (std::ostream &, const Hornsat &);
};

#endif
