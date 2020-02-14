%{

#include <stdio.h>
#include <stdlib.h>

    unsigned _varwidth = 4000;
    unsigned proof_num = 0;

    extern int yylex();
    extern int yyparse();
    extern FILE* yyin;

    void yyerror(const char* s);

    %}

%union {
    int ival;
    char * sval;
}

%token<sval> MINUS_SYM REL_SYM OP_SYM T_PROOF_RULE T_NAME
%token PAREN_LEFT PAREN_RIGHT T_LET COMMA COLON VDASH SEMI_COLON
%type<ival> expressions 
%type<ival> hyps

%start parse

%%

parse:
{ printf("\\documentclass[varwidth=%dpt]\{standalone}\
\n\\usepackage{ebproof}\
\n\\usepackage{amssymb}\
\n\\usepackage{amsmath}\
\n\\usepackage{xcolor}\
\n\\begin{document}\n", _varwidth); }
proofs
{ printf("\n\\end{document}\n"); return 0; }
;

proofs:
proof
| proof proofs
;

interpolant:
{ printf("\\textcolor{red}{"); } SEMI_COLON expression { printf("}"); }
; 

proof:
{ printf("Proof number %d:\\begin{prooftree}\n", ++proof_num); }
T_PROOF_RULE COLON hyps { printf("\\infer%d[%s]{", $4, $2); } VDASH expression interpolant { printf("}\n"); }
{ printf("\\end{prooftree}\n"); }
;

expression:
T_NAME { printf("(%s)", $1); }
| PAREN_LEFT T_LET PAREN_LEFT { printf("(let ("); } bindings PAREN_RIGHT expression PAREN_RIGHT { printf(")"); }
| PAREN_LEFT MINUS_SYM    { printf("(%s", $2);  } expressions PAREN_RIGHT { printf(")"); }
| PAREN_LEFT REL_SYM      { printf("(%s", $2);  } expressions PAREN_RIGHT { printf(")"); }
| PAREN_LEFT OP_SYM       { printf("(%s", $2);  } expressions PAREN_RIGHT { printf(")"); }
| PAREN_LEFT T_NAME       { printf("(%s", $2);  } expressions PAREN_RIGHT { printf(")"); }
;

hyps: { $$ = 0; }
| { printf("\\infer0[x]{"); } expression interpolant { printf("}\n"); } COMMA hyps { $$ = $6 + 1; }
;

expressions:
expression { $$ = 1; }
| expression expressions { $$ = $2 + 1; }
;

bindings:
PAREN_LEFT T_NAME { printf("(%s", $2); } expression PAREN_RIGHT { printf(")"); }
| bindings PAREN_LEFT T_NAME { printf("(%s", $3); } expression PAREN_RIGHT { printf(")"); }
;

%%

int main() {
    yyin = stdin;

    do {
	yyparse();
    } while(!feof(yyin));

    return 0;
}

void yyerror(const char* s) {
    fprintf(stderr, "Parse error: %s\n", s);
    exit(1);
}
