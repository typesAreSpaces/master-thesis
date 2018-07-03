#ifndef _HORNSAT_
#define _HORNSAT_

#include <iostream>
#include <queue>
#define MAX 100

typedef struct clause{
  int clauseno;
  struct clause * next;
} clause;

typedef struct literal{
  bool val;
  struct clause * clauselist;
} literal;

typedef struct count{
  int listOfClauses[MAX];
} count;

typedef std::queue<int> queuei;

class Hornclause{
 private:
  literal listOfLiterals[MAX];
  queuei q;
  count numargs, poslitlist;
  bool consistent;
  int numpos, numDisPosLiterals, numBasicHornClauses;
 public:
  Hornclause(std::istream &);
  ~Hornclause();
  void addClauseToLiteral(int, int);
  void satisfiable();
  bool isConsistent();
  std::ostream & printAssignment(std::ostream &);
};

#endif
