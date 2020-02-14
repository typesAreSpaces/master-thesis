%option noyywrap

%{
#include <stdio.h>

#define YY_DECL int yylex()

#include "z3-proof-parser.tab.h"

%}

%%

[ \t]	; // ignore all whitespace
"true-axiom"      {yylval.sval = strdup(yytext); return T_PROOF_RULE;}
"asserted"        {yylval.sval = strdup(yytext); return T_PROOF_RULE;}
"goal"            {yylval.sval = strdup(yytext); return T_PROOF_RULE;}
"mp"              {yylval.sval = strdup(yytext); return T_PROOF_RULE;}
"refl"            {yylval.sval = strdup(yytext); return T_PROOF_RULE;}
"symm"            {yylval.sval = strdup(yytext); return T_PROOF_RULE;}
"trans"           {yylval.sval = strdup(yytext); return T_PROOF_RULE;}
"trans*"          {yylval.sval = strdup(yytext); return T_PROOF_RULE;}
"monotonicity"    {yylval.sval = strdup(yytext); return T_PROOF_RULE;}
"quant-intro"     {yylval.sval = strdup(yytext); return T_PROOF_RULE;}
"distributivity"  {yylval.sval = strdup(yytext); return T_PROOF_RULE;}
"and-elim"        {yylval.sval = strdup(yytext); return T_PROOF_RULE;}
"not-or-elim"     {yylval.sval = strdup(yytext); return T_PROOF_RULE;}
"rewrite"         {yylval.sval = strdup(yytext); return T_PROOF_RULE;}
"rewrite*"        {yylval.sval = strdup(yytext); return T_PROOF_RULE;}
"pull-quant"      {yylval.sval = strdup(yytext); return T_PROOF_RULE;}
"push-quant"      {yylval.sval = strdup(yytext); return T_PROOF_RULE;}
"elim-unused"     {yylval.sval = strdup(yytext); return T_PROOF_RULE;}
"der"             {yylval.sval = strdup(yytext); return T_PROOF_RULE;}
"quant-inst"      {yylval.sval = strdup(yytext); return T_PROOF_RULE;}
"hypothesis"      {yylval.sval = strdup(yytext); return T_PROOF_RULE;}
"lemma"           {yylval.sval = strdup(yytext); return T_PROOF_RULE;}
"unit-resolution" {yylval.sval = strdup(yytext); return T_PROOF_RULE;}
"iff-true"        {yylval.sval = strdup(yytext); return T_PROOF_RULE;}
"iff-false"       {yylval.sval = strdup(yytext); return T_PROOF_RULE;}
"commutativity"   {yylval.sval = strdup(yytext); return T_PROOF_RULE;}
"def-axiom"       {yylval.sval = strdup(yytext); return T_PROOF_RULE;}
"intro-def"       {yylval.sval = strdup(yytext); return T_PROOF_RULE;}
"apply-def"       {yylval.sval = strdup(yytext); return T_PROOF_RULE;}
"iff~"            {yylval.sval = strdup(yytext); return T_PROOF_RULE;}
"nnf-pos"         {yylval.sval = strdup(yytext); return T_PROOF_RULE;}
"nnf-neg"         {yylval.sval = strdup(yytext); return T_PROOF_RULE;}
"sk"              {yylval.sval = strdup(yytext); return T_PROOF_RULE;}
"mp~"             {yylval.sval = strdup(yytext); return T_PROOF_RULE;}
"th-lemma"        {yylval.sval = strdup(yytext); return T_PROOF_RULE;}
"hyper-res"       {yylval.sval = strdup(yytext); return T_PROOF_RULE;}
"add-assume"      {yylval.sval = strdup(yytext); return T_PROOF_RULE;}
"add-lemma"       {yylval.sval = strdup(yytext); return T_PROOF_RULE;}
"add-th-assume"   {yylval.sval = strdup(yytext); return T_PROOF_RULE;}
"add-th-lemma"    {yylval.sval = strdup(yytext); return T_PROOF_RULE;}
"del-redundant"   {yylval.sval = strdup(yytext); return T_PROOF_RULE;}
"proof-trail"     {yylval.sval = strdup(yytext); return T_PROOF_RULE;}
"("		  {return PAREN_LEFT;}
")"		  {return PAREN_RIGHT;}
","		  {return COMMA;}
"<"               {yylval.sval = strdup(yytext); return REL_SYM;}
">"               {yylval.sval = strdup(yytext); return REL_SYM;}
"<="              {yylval.sval = strdup(yytext); return REL_SYM;}
">="              {yylval.sval = strdup(yytext); return REL_SYM;}
"=="              {yylval.sval = strdup(yytext); return REL_SYM;}
"!="              {yylval.sval = strdup(yytext); return REL_SYM;}
"+"               {yylval.sval = strdup(yytext); return OP_SYM;}
"*"               {yylval.sval = strdup(yytext); return OP_SYM;}
"-"               {yylval.sval = strdup(yytext); return MINUS_SYM;}
"/"               {yylval.sval = strdup(yytext); return OP_SYM;}
[a-zA-Z0-9_]+     {yylval.sval = strdup(yytext); return T_NAME;}

%%
