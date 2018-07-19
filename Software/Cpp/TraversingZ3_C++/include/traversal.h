#ifndef _TRAVERSAL_
#define _TRAVERSAL_

#include "z3.h"
#include "z3++.h"

void exitf(const char*);
void unreachable();
void display_symbol(Z3_context, FILE *, Z3_symbol);
void display_sort(Z3_context, FILE *, Z3_sort);
void display_ast(Z3_context, FILE *, Z3_ast);
void visit(z3::expr const &);

#endif
