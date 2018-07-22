#ifndef CONG_CLOSURE
#define CONG_CLOSURE

#include <iostream>
#include <set>
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

class CongruenceClosure : public SignatureTable {
 public:
  CongruenceClosure(std::istream &);
  ~CongruenceClosure();
  void algorithm();
  std::ostream & print(std::ostream &);
  bool checkCorrectness();
};

#endif
