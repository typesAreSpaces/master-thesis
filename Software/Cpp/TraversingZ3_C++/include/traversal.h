#ifndef _TRAVERSAL_
#define _TRAVERSAL_

#include "z3++.h"
#include <stack>

void visit(z3::expr const &);
void visitWithStack(z3::expr const &);

#endif
