#ifndef _CONG_CLOSURE
#define _CONG_CLOSURE

#include "SignatureTable.h"

typedef std::set<Vertex*> Pending;
typedef std::set<std::pair<Vertex*, Vertex*> > Combine;

class CongruenceClosure : public SignatureTable {
 private:
  void init(Z3_context);
	
 public:
	CongruenceClosure(Z3_context, Z3_ast, std::set<std::string> &);
  CongruenceClosure(Z3_context, Z3_ast);
  CongruenceClosure(std::istream &);
  ~CongruenceClosure();
  void algorithm();
  bool checkCorrectness();
	friend std::ostream & operator << (std::ostream &, CongruenceClosure &);
};

#endif
