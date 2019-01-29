#ifndef _DISPLAY_AST_
#define _DISPLAY_AST_

#include <iostream>
#include "z3.h"

// Taken from the Z3 project
// File: test_capi.c

void exitf(const char *);
void unreachable();
void display_symbol(Z3_context, FILE *, Z3_symbol);
void display_sort(Z3_context, FILE *, Z3_sort);
void display_ast(Z3_context, FILE *, Z3_ast);

#endif
