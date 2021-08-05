#ifndef _DISEQS_FLATTN_
#define _DISEQS_FLATTN_

#include <iostream>
#include <set>
#include <z3++.h>

struct DisequalitiesFlattener {

  z3::context & ctx;
  std::set<unsigned> previous_ids;

  z3::expr freshConstant(z3::expr const &);
  void updateFlatten(z3::expr const &);

  z3::expr_vector    flatten;
  z3::expr_vector    flatten_persistent_from;
  z3::expr_vector    flatten_persistent_to;

  DisequalitiesFlattener(z3::expr_vector const &);
  friend std::ostream & operator << (std::ostream &, DisequalitiesFlattener const &);
};

#endif
