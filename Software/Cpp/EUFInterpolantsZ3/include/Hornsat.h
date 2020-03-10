#ifndef _HORNSAT_
#define _HORNSAT_
#define FALSELITERAL 0
#define DEBUG_DESTRUCTORS false

#include <iostream>
#include <queue>
#include "CongruenceClosureDST.h"
#include "CongruenceClosureNO.h"
#include "CongruenceClosureExplain.h"
#include "HornClauses.h"
#include "Replacement.h"

struct Clause {
  unsigned clause_id;
  struct Clause * next;
  Clause(unsigned id, struct Clause * clause) : clause_id(id), next(clause){}
  ~Clause(){
#if DEBUG_DESTRUCTORS
    std::cout << "Done ~Clause with " << clause_id  << std::endl;
#endif
  }
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
  ~Literal(){
#if DEBUG_DESTRUCTORS
    std::cout << "Done ~Literal with " << literal_id  << std::endl;
#endif
  }
};

struct ClassListPos {
  Literal * lit_pointer;
  SideOfEquation eq_side;
  ClassListPos(Literal * lit_pointer, SideOfEquation eq_side) :
    lit_pointer(lit_pointer), eq_side(eq_side){}
  friend std::ostream & operator << (std::ostream & os, const ClassListPos & clp){
    os << *(clp.lit_pointer) << (clp.eq_side == LHS ? " LHS" : " RHS");
    return os;
  }
  ~ClassListPos(){
#if DEBUG_DESTRUCTORS
    std::cout << "Done ~ClassListPos with " << lit_pointer << (eq_side == LHS ? " LHS" : " RHS") << std::endl;
#endif
  }
};

typedef std::vector<std::vector<ClassListPos> > ClassList;

class Hornsat {
  const z3::expr_vector & subterms;
  bool                    consistent;
  unsigned                num_pos, num_hcs, num_literals;
  std::vector<Literal>    list_of_literals;
  ClassList               class_list;
  // facts is a queue of all the (temporary)
  // literals that have value true
  std::queue<unsigned> facts;
  std::vector<unsigned> num_args, pos_lit_list;

  void unionupdate(UnionFind &, unsigned, unsigned);
  void update(CongruenceClosure &, std::list<unsigned> &, unsigned, unsigned);
  void congclosure(CongruenceClosure &, std::list<unsigned> &);
  
 public:
  // Hornsat(std::istream &);
  Hornsat(const HornClauses &, UnionFind &);
  ~Hornsat();
  void satisfiable();
  std::vector<Replacement> satisfiable(CongruenceClosure &);
  bool isConsistent();
  
  friend std::ostream & operator << (std::ostream &, const Hornsat &);
};

#endif
