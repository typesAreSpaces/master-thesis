#ifndef _CONG_CLOSURE
#define _CONG_CLOSURE

#include <map>
#include "Terms.h"
#include "SignatureTable.h"

// SymbolLocation : SymbolName -> Set of Locations
// Map to keep track the location (position in the `terms' data structure)
// of names inside expressions 
typedef std::vector<Term*> Pending;
typedef std::vector<std::pair<Term*, Term*> > Combine;

class CongruenceClosure : public Terms {
 public:
  CongruenceClosure(z3::context &, const z3::expr &, unsigned);
  CongruenceClosure(z3::context &, const z3::expr &, const UncommonSymbols &, unsigned);
  ~CongruenceClosure();

  void buildCongruenceClosure();
  bool checkCorrectness();
  void transferEqClassAndPreds(const CongruenceClosure &);
  void transferEqClass(const CongruenceClosure &);
  void transferPreds(const CongruenceClosure &);
  void addEquation(Term *, Term *);
  void addEquation(unsigned, unsigned);
  
  const SymbolLocations & getSymbolLocations();
  
  friend std::ostream & operator << (std::ostream &, CongruenceClosure &);
  
 private:
  SignatureTable  sigTable;
  void            processEquations();
  unsigned        name;
};

#endif
