#ifndef _OCT_PARSER_
#define _OCT_PARSER_

#include <z3++.h>
#include <iostream>
#include <unordered_map>
#include <set>
#include <vector>
#include "Bound.h"
#include "Octagon.h"

class OctagonParser {

  z3::context &   ctx;
  z3::expr_vector z3_variables;

  std::unordered_map<unsigned, VarValue> id_table;
  std::set<unsigned>                     checked_ids;
  std::vector<Bound>                     bounds;
  
  public:
    OctagonParser(z3::expr_vector const &);

    friend std::ostream & operator << (std::ostream &, OctagonParser const &);

};

#endif
