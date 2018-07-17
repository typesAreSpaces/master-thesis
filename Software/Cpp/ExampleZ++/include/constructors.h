#ifndef _CONSTRUCTORS_
#define _CONSTRUCTORS_

#include "z3.h"
#include "z3++.h"

Z3_ast mk_var(Z3_context, const char *, Z3_sort);
Z3_ast mk_int_var(Z3_context, const char *);
Z3_ast mk_int(Z3_context, int);

#endif
