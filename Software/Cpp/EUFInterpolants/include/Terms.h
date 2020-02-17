#ifndef _TERMS_
#define _TERMS_
#define notInSet(y, x) x.find(y) == x.end()

#include <stack>
#include <map>
#include <set>
#include <z3++.h>
#include "Term.h"
#include "UnionFind.h"

// The following structure keeps track of all the positions involving equations
// inside the equivalence class of terms with the given symbol name
// i.e. f -> <location(f(x)), location(f(y)), location(f(f(x)))> in SymbolLocations
typedef std::map<std::string, std::vector<unsigned> > SymbolLocations;
typedef std::pair<z3::expr, z3::expr>                 Equation;
typedef std::pair<z3::expr, z3::expr>                 Disequation;
typedef std::vector<Equation>                         Equations;
typedef std::vector<Disequation>                      Disequations;
typedef std::set<std::string>                         UncommonSymbols;

class Terms {

  void exitf(const char *);
  void unreachable();
  void extractSymbolsAndTerms(const z3::expr &, UncommonSymbols &);
  void extractTerms(const z3::expr &);
  void removeSymbols(const z3::expr &, UncommonSymbols &);
    
protected:
  z3::context &            ctx;
  unsigned                 root_num;
  std::vector<Equation>    equations;
  std::vector<Disequation> disequations;
  UncommonSymbols          symbols_to_elim;

  std::vector<Term*>       terms;
  UnionFind                equivalence_class;
  SymbolLocations          symbol_locations;
  
public:
  Terms(z3::context &, const z3::expr &);
  Terms(z3::context &, const z3::expr &, const UncommonSymbols &);
  ~Terms();

  std::vector<Term*> &    getTerms();
  void                    setEquivalenceClass(UnionFind &);
  UnionFind &             getEquivalenceClass();
  const UnionFind         getDeepEquivalenceClass() const;
  Term *                  getOriginalTerm(unsigned) const;
  Term *                  getReprTerm (unsigned);
  Term *                  getReprTerm(Term*);
  void                    merge(Term*, Term*);
  void                    merge(unsigned, unsigned);
  void                    rotate(Term*, Term*);
  unsigned                getRootNum();
  z3::context &           getCtx();
  const UncommonSymbols & getSymbolsToElim();
  const Equations &       getEquations();
  const Disequations &    getDisequations();
  bool                    areEqual(Term *, Term *);
  bool                    areEqual(unsigned, unsigned);
  void                    identifyCommonSymbols();
  
  friend std::ostream & operator <<(std::ostream &, const Terms &);
};


#endif
