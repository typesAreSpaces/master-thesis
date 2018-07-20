#ifndef CONG_CLOSURE
#define CONG_CLOSURE

#include <iostream>
#include <set>
#include "z3++.h"
#include "GTerms.h"
#include "SignatureTable.h"
#include "Vertex.h"

typedef std::set<Vertex*> Pending;
typedef std::set<std::pair<Vertex*, Vertex*> > Combine;
extern bool traceMerge;
extern bool traceCombine;
extern bool tracePending;
extern bool traceEC;
extern bool traceSigTable;

class CongruenceClosure{
 private:
  GTerms & terms;
  SignatureTable & sigTable;
 public:
  CongruenceClosure(GTerms &, SignatureTable &, std::istream &);
  ~CongruenceClosure();
  void algorithm();
  std::ostream & print(std::ostream &);
};

#endif
