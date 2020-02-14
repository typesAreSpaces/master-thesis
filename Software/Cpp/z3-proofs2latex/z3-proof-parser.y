%{

#include <stdio.h>
#include <stdlib.h>

    extern int yylex();
    extern int yyparse();
    extern FILE* yyin;

    void yyerror(const char* s);
    %}

%union {
    int ival;
    char * sval;
}

%token<ival> T_INT
%token<sval> T_NAME T_PROOF_RULE END REL_SYM OP_SYM MINUS_SYM
%token PAREN_LEFT PAREN_RIGHT COMMA 
%left REL_SYM OP_SYM MINUS_SYM
%type<ival> proof_args

%start parse

%%

parse:
{ printf("\\documentclass{standalone}\n\\usepackage{ebproof}\n\\begin{document}\n\\begin{prooftree}"); }
proof_term
{ printf("\\end{prooftree}\n\\end{document}\n"); }
;

proof_term:
T_PROOF_RULE PAREN_LEFT proof_args { printf("\\infer%d[%s]{", $3, $1); } consequent_term PAREN_RIGHT { printf("}"); }
;

proof_args: { $$ = 0; }
| proof_term COMMA proof_args { $$ = $3 + 1; }
;

consequent_term:
T_NAME { printf("%s", $1); }
| T_NAME PAREN_LEFT { printf("%s(", $1); } consequent_args PAREN_RIGHT { printf(")"); }
| PAREN_LEFT { printf("("); } consequent_term PAREN_RIGHT { printf(")"); }
| MINUS_SYM { printf("%s", $1); } consequent_term
| consequent_term MINUS_SYM { printf("%s", $2); } consequent_term
| consequent_term REL_SYM { printf("%s", $2); } consequent_term
| consequent_term OP_SYM { printf("%s", $2); } consequent_term
;

consequent_args: consequent_term
| consequent_term COMMA { printf(", "); } consequent_args

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
