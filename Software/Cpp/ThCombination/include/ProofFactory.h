#ifndef _PROOF_FACTORY_
#define _PROOF_FACTORY_
#define _DEBUG_CLAUSE_PROOF_ 0

#include <iostream>
#include <cstdlib>
#include <memory>
#include <array>
#include <fstream>
#include <sstream>
#include <string>
#include <list>
#include <vector>
#include <algorithm>

struct ResolutionProof {
  std::list<unsigned> pivots;
  ResolutionProof();
  void addPivot(unsigned);
};

class ClauseProof : public ResolutionProof {

  unsigned                       id;
  std::list<int>                 literals;
  std::list<ClauseProof const *> clause_subproofs;

  public:
  ClauseProof(unsigned);

  void addLiteral(int);
  void addSubproof(ClauseProof const *);
  void setLiterals(ClauseProof const &);
  void updateResolution(int, ClauseProof const &);
  friend std::ostream & operator << (std::ostream &, ClauseProof const &);
};

class LitProof : public ResolutionProof { 

  // The id is: 
  // 2*lit if lit is positive
  // 2*lit + 1 if lit is negative
  unsigned                    id;
  std::list<LitProof const *> lit_subproofs;
  ClauseProof const *         clause_subproof;

  public:
  LitProof(unsigned);
  unsigned getId() const;
  void addSubproof(LitProof const *);
  void setClauseProof(ClauseProof const *);
  friend std::ostream & operator << (std::ostream &, LitProof const &);
};

class ConflictProof : public ResolutionProof {

  std::list<LitProof const *> lit_subproofs;
  ClauseProof const *         clause_subproof;

  public:
  ConflictProof();
  void addSubproof(LitProof const *);
  void setClauseProof(ClauseProof const *);
  friend std::ostream & operator << (std::ostream &, ConflictProof const &);
};

class ProofFactory {

  typedef std::vector<ClauseProof> ClauseProofs;
  typedef std::vector<LitProof>    LitProofs;

  ClauseProofs  clause_proofs;
  LitProofs     lit_proofs;
  ConflictProof conflict_proof;

  std::string exec(const char *);

  public:
  ProofFactory();
  void initLitProofs(unsigned);
};

#endif
