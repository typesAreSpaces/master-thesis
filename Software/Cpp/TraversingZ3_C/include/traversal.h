#ifndef _TRAVERSAL_
#define _TRAVERSAL_

//#include "z3.h"
#include "z3++.h"

void exitf(const char*);
void unreachable();
void visit_symbol(Z3_context, FILE *, Z3_symbol);
void visit_sort(Z3_context, FILE *, Z3_sort);
void visit(Z3_context, FILE *, Z3_ast);

#endif
