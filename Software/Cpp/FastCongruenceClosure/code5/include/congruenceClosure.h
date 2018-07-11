#ifndef CONG_CLOSURE
#define CONG_CLOSURE

#include <iostream>
#include <set>
#include "GTerms.h"
#include "signatureTable.h"
#include "vertex.h"

typedef std::set<Vertex*> Pending;
typedef std::set<std::pair<Vertex*, Vertex*> > Combine;

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
