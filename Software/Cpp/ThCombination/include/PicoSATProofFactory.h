#ifndef _PICO_SAT_PF_
#define _PICO_SAT_PF_

#define _DEBUG_PICO_SAT_PF_ 1

#include <iostream>
#include <cstdlib>
#include <memory>
#include <array>
#include <fstream>
#include <list>
#include <vector>
#include <algorithm>
#include <istream>
#include <sstream>
#include <string>
#include <set>

class PicoProofFactory {

  std::string exec(const char *);
  
  struct PicoResolutionProof : public std::vector<int> {
    int pivot, subproof_1, subproof_2;

    public:
      PicoResolutionProof();

      void updatePivot(int);
      void addLiteral(int);
      void updateSubproofs(int, int);
      void updatePivot(PicoProofFactory const &);
  };

  std::vector<PicoResolutionProof> proof_table;

  public:
    PicoProofFactory();

  friend std::ostream & operator << (std::ostream &, PicoProofFactory const &);
};

#endif
