#ifndef _CONG_CLOSURE
#define _CONG_CLOSURE

#include <stack>
#include <map>
#include "Terms.h"
#include "SignatureTable.h"

// SymbolLocation : SymbolName -> Set of Locations
// Map to keep track the location (position in the `terms' data structure)
// of names inside expressions 
typedef std::map<std::string, std::vector<unsigned> > SymbolLocations;
typedef std::vector<Term*> Pending;
typedef std::vector<std::pair<Term*, Term*> > Combine;

class CongruenceClosure : public Terms {	
 public:
  CongruenceClosure(z3::context &, const z3::expr &);
  CongruenceClosure(z3::context &, const z3::expr &, const UncommonSymbols &);
  ~CongruenceClosure();

  void identifyCommonSymbols();
  void buildCongruenceClosure();
  bool checkCorrectness();
  void transferEqClassAndPreds(const CongruenceClosure &);
  void transferEqClass(const CongruenceClosure &);
  void transferPreds(const CongruenceClosure &);
  
  const SymbolLocations & getSymbolLocations();
  
  friend std::ostream & operator << (std::ostream &, CongruenceClosure &);
  
 private:
  SignatureTable  sigTable;
  SymbolLocations symbol_locations;
  void            init();
};

#endif
