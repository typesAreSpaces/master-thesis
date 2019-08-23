#ifndef _CONG_CLOSURE
#define _CONG_CLOSURE

#include "Terms.h"
#include "SignatureTable.h"

typedef std::vector<Term*> Pending;
typedef std::vector<std::pair<Term*, Term*> > Combine;

class CongruenceClosure : public Terms {
 private:
  SignatureTable sigTable;
  void init();
	
 public:
  CongruenceClosure(z3::context &, const z3::expr &);
  CongruenceClosure(z3::context &, const z3::expr &, const std::set<std::string> &);
  ~CongruenceClosure();
  void algorithm();
  bool checkCorrectness();
  friend std::ostream & operator << (std::ostream &, const CongruenceClosure &);
};

#endif
