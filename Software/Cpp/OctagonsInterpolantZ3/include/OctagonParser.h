#ifndef _OCT_PARSER_
#define _OCT_PARSER_
#define DEBUG_OCT_PAR_CONST 1

#include <z3++.h>
#include <iostream>
#include <unordered_map>
#include <set>
#include <vector>
#include "Bound.h"
#include "Bounds.h"
#include "Octagon.h"

#define inSet(value, set) (set.find(value) != set.end())

// The index is the hash of a z3::expr
typedef std::unordered_map<unsigned, VarValue> IdTable;

class OctagonParser {

  z3::context &   ctx;
  z3::expr_vector z3_variables;

  UtvpiPosition      id_generator;
  IdTable            id_table;
  Bounds             bounds;

  void checkExprId(z3::expr const &);
  UtvpiPosition setBoundWith1Var (bool, z3::expr const &);
  UtvpiPosition setBoundWith2Vars(bool, z3::expr const &);
  
  public:
    OctagonParser(z3::expr_vector const &);

    friend std::ostream & operator << (std::ostream &, OctagonParser const &);

};

#endif
