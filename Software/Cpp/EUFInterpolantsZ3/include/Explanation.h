#ifndef _EXPLAINATION_
#define _EXPLAINATION_

#define IsMember(set, elem) set.find(elem) != set.end()

#include <set>
#include <z3++.h>

class Explanation 
{

  z3::expr_vector    result;
  std::set<unsigned> current_ids;

  public:
  Explanation(z3::context &);
  ~Explanation();
  void add(z3::expr_vector const &);
  z3::expr_vector get() const;
};

#endif
