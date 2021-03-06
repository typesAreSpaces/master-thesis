#ifndef _HORN_CLAUSE_
#define _HORN_CLAUSE_

#include "Terms.h"
#include <assert.h>
#include <vector>
#include <utility>

typedef std::pair<Vertex*, Vertex*> equality;

class HornClause{	
 private:
  static UnionFind            global_UF;
  static bool                 is_first_time;
  static std::vector<Vertex*> global_terms;
  UnionFind                   local_UF;	
  bool                        antecedent_boolean_value, consequent_boolean_value;
  std::vector<equality>       antecedent;
  equality                    consequent;
	
 public:
  HornClause(UnionFind &, std::vector<equality> &, equality &, std::vector<Vertex*> &);
  HornClause(UnionFind &, Vertex*, Vertex*, std::vector<Vertex*> &, bool);
  ~HornClause();
  void normalize();
  bool checkTriviality();
  bool getAntecedentValue();
  bool getConsequentValue();
  bool getMaximalConsequent();
  std::vector<equality> & getAntecedent();
  equality & getConsequent();
  UnionFind & getLocalUF();
  static UnionFind & getGlobalUF();
  Vertex * getVertex(unsigned);
  Vertex * getVertex(Vertex *);
  friend bool operator <(HornClause &, HornClause &);
  friend bool operator >(HornClause &, HornClause &);
  friend std::ostream & operator << (std::ostream &, HornClause &);
};

#endif
