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

struct LitProof { 

  unsigned                    id;
  bool                        polarity;
  std::list<LitProof const *> lit_subproofs;
  ClauseProof const *         clause_subproof;

  LitProof();
};

struct ConflictProof {

  unsigned                    id;
  bool                        polarity;
  std::list<LitProof const *> lit_subproofs;
  ClauseProof const *         clause_subproof;

  ConflictProof();
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
};

#endif
