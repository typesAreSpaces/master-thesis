%{

#include <stdio.h>
#include <stdlib.h>

    unsigned _varwidth = 2000;
    unsigned new_proof_tree = 0;
    unsigned new_term_tree = 0;

    extern int yylex();
    extern int yyparse();
    extern FILE* yyin;

    void yyerror(const char* s);

    void term_begin(char * s, char extra){
	if(new_proof_tree == 0){
	    if(new_term_tree == 0)
		printf("$");
	    printf("%c%s", extra, s);
	}
	else{
	    if(new_term_tree == 0)
		printf("\\infer0[definition]{");
	    printf("\\hspace{0.001cm}%c%s", extra, s);
	}
	new_term_tree++;
    }
    void term_end(char extra){
	new_term_tree--;
	printf("%c", extra);
	if(new_proof_tree == 0){
	    if(new_term_tree == 0)
		printf("$");
	}
	else{
	    if(new_term_tree == 0)
		printf("}");
	}
    }

    void proof_begin(){
        if(new_proof_tree == 0)
	    printf("\\begin{prooftree}");
	new_proof_tree++;
    }

    void proof_end(int num_args, char * proof_name){
        new_proof_tree--;
	printf("\\infer%d[%s]{}", num_args, proof_name);
	if (new_proof_tree == 0)
	    printf("\\end{prooftree}");
    }

    %}

%union {
    int ival;
    char * sval;
}

%token<sval> MINUS_SYM REL_SYM OP_SYM T_PROOF_RULE T_NAME
%token PAREN_LEFT PAREN_RIGHT T_LET
%type<ival> expressions

%start parse

%%

parse:
{ printf("\\documentclass[varwidth=%dpt]\{standalone}\
\n\\usepackage{ebproof}\
\n\\usepackage{amssymb}\
\n\\usepackage{amsmath}\
\n\\begin{document}\n", _varwidth); }
expression
{ printf("\n\\end{document}\n"); }
;

expression:
T_NAME { term_begin($1, '('); term_end(')'); }
| PAREN_LEFT T_LET PAREN_LEFT bindings PAREN_RIGHT expression PAREN_RIGHT
| PAREN_LEFT MINUS_SYM    { term_begin($2, '(');  } expressions PAREN_RIGHT { term_end(')');     }
| PAREN_LEFT REL_SYM      { term_begin($2, '(');  } expressions PAREN_RIGHT { term_end(')');     }
| PAREN_LEFT OP_SYM       { term_begin($2, '(');  } expressions PAREN_RIGHT { term_end(')');     }
| PAREN_LEFT T_PROOF_RULE { proof_begin();        } expressions PAREN_RIGHT { proof_end($4, $2); }
| PAREN_LEFT T_NAME       { term_begin($2, '(');  } expressions PAREN_RIGHT { term_end(')');     }
;

expressions:
expression { $$ = 1; }
| expression expressions { $$ = $2 + 1; }
;

bindings:
PAREN_LEFT T_NAME expression PAREN_RIGHT { printf("\n\nProof/Definition of %s\n\n", $2); }
| PAREN_LEFT T_NAME expression PAREN_RIGHT { printf("\n\nProof/Definition of %s\n\n", $2); } bindings
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
