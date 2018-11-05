#ifndef _CONG_CLOSURE
#define _CONG_CLOSURE

#include "SignatureTable.h"

typedef std::set<Vertex*> Pending;
typedef std::set<std::pair<Vertex*, Vertex*> > Combine;
extern bool traceMerge;
extern bool traceCombine;
extern bool tracePending;
extern bool traceEC;
extern bool traceSigTable;

class CongruenceClosure : public SignatureTable {
 private:
  void init(Z3_context);
 public:
	CongruenceClosure(Z3_context, Z3_ast, std::set<std::string> &);
  CongruenceClosure(Z3_context, Z3_ast);
  CongruenceClosure(std::istream &);
  ~CongruenceClosure();
  void algorithm();
  std::ostream & print(std::ostream &);
  bool checkCorrectness();
};

#endif
