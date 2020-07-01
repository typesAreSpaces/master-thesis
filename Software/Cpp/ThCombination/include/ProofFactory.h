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

class ClauseProof {

  unsigned                       id;
  std::list<int>                 literals;
  std::list<ClauseProof const *> clause_subproofs;

  public:
  ClauseProof(unsigned);

  void addLiteral(int);
  void addSubproof(ClauseProof const *);
  void updateLiterals(ClauseProof const &);
  void updateResolution(int, ClauseProof const &);
  friend std::ostream & operator << (std::ostream &, ClauseProof const &);
};

class LitProof { 

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
  void updateClauseProof(ClauseProof const *);
};

class ConflictProof {

  // The id is: 
  // 2*lit if lit is positive
  // 2*lit + 1 if lit is negative
  unsigned                    id;
  std::list<LitProof const *> lit_subproofs;
  ClauseProof const *         clause_subproof;

  public:
  ConflictProof();
};

class ProofFactory {

  typedef std::vector<ClauseProof> ClauseProofs;
  class LitProofs : public std::vector<LitProof> {
    public:
    void if_enough_push_back_otherwise_resize(LitProof const &);
  };

  ClauseProofs  clause_proofs;
  LitProofs     lit_proofs;
  ConflictProof conflict_proof;

  std::string exec(const char *);

  public:
  ProofFactory();
};

#endif
