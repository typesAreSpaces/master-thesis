#ifndef _TRAVERSAL_
#define _TRAVERSAL_

#include "z3++.h"
#include <stack>
#include <map>
#include <set>

void visit(z3::expr const &);
void visitWithStack(z3::expr const &);
void visitPostOrderWithStack(z3::expr const &);
void insert(z3::expr const & e, std::stack<z3::expr> &, std::map<unsigned, int> &);
void move(std::stack<z3::expr> &);

#endif
