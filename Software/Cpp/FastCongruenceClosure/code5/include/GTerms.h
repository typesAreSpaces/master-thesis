#ifndef _GTERMS_
#define _GTERMS_

#include <iostream>
#include <vector>
#include "vertex.h"

class GTerms{
 private:
  std::vector<Vertex*> terms;
 public:
  GTerms(std::istream &);
  ~GTerms();
  std::ostream & print(std::ostream &);
};

#endif 
