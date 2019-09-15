#ifndef _CONG_CLOSURE
#define _CONG_CLOSURE

#include "Terms.h"
#include "SignatureTable.h"

typedef std::vector<Term*> Pending;
typedef std::vector<std::pair<Term*, Term*> > Combine;

class CongruenceClosure : public Terms {	
 public:
  CongruenceClosure(z3::context &, const z3::expr &);
  CongruenceClosure(z3::context &, const z3::expr &, const UncommonSymbols &);
  ~CongruenceClosure();
  
  void buildCongruenceClosure();
  bool checkCorrectness();
  void transferEqClassAndPreds(const CongruenceClosure &);
  void transferEqClass(const CongruenceClosure &);
  void transferPreds(const CongruenceClosure &);
  
  friend std::ostream & operator << (std::ostream &, CongruenceClosure &);
  
 private:
  SignatureTable sigTable;
  void           init();
};

#endif
