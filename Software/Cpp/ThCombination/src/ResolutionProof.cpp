#include "ResolutionProof.h"

ResolutionProof::ResolutionProof(std::string const & cnf_file)
{
  system(cnf_file.c_str());
}
