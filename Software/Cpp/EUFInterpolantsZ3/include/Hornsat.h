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
  bool val;
  struct Clause * clause_list;
  Literal(unsigned literal_id, bool val, struct Clause * clause_list) :
    literal_id(literal_id),
    val(val), clause_list(clause_list){}
  Literal() : Literal(curr_num_literals++, false, nullptr) {}
};

struct Count {
  std::vector<unsigned> list_of_clauses;
  void insert(unsigned index_hc, unsigned element){
    list_of_clauses[index_hc] = element;
  }
  unsigned get(unsigned index_hc){
    return list_of_clauses[index_hc];
  }
  void resize(unsigned i){
    list_of_clauses.resize(i);
  }
  unsigned size() const {
    return list_of_clauses.size();
  }
};

class Hornsat {
  std::vector<Literal> list_of_literals;
  std::queue<unsigned> facts;
  Count num_args, pos_lit_list;
  bool consistent;
  unsigned num_pos;
 public:
  Hornsat(std::istream &);
  Hornsat(const HornClauses &);
  ~Hornsat();
  void satisfiable();
  bool isConsistent();
  friend std::ostream & operator << (std::ostream &, const Hornsat &);
};

#endif
