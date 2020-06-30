#ifndef _RES_PROOF_
#define _RES_PROOF_

#include <iostream>
#include <cstdlib>
#include <memory>
#include <array>
#include <fstream>
#include <sstream>
#include <string>

class ResolutionProof {
  class LitProof { 

  };

  class ClauseProof {

  };

  std::string exec(const char *);

  public:
  ResolutionProof(unsigned original_num_clauses);
};

#endif
