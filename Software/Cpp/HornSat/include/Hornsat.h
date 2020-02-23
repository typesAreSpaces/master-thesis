#ifndef _HORNSAT_
#define _HORNSAT_
#define FALSELITERAL 0

#include <iostream>
#include <queue>
#include <vector>


struct Clause {
  unsigned clause_id;
  struct Clause * next;
Clause(unsigned id, struct Clause * clause) : clause_id(id), next(clause){}
};

struct Literal {
  bool val;
  struct Clause * clause_list;
  Literal(bool val, struct Clause * clause_list) : val(val), clause_list(clause_list){}
  Literal() : Literal(false, nullptr) {}
};

struct Count {
  std::vector<unsigned> list_of_clauses;
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
  ~Hornsat();
  void addClauseToLiteral(unsigned, unsigned);
  void satisfiable();
  bool isConsistent();
  friend std::ostream & operator << (std::ostream &, const Hornsat &);
};

#endif
