Z3DIR = /home/jose/Documents/GithubProjects/z3/build/libz3.so

all: proof_python

z3-proof-parser.tab.c z3-proof-parser.tab.h:	z3-proof-parser.y
	bison -d z3-proof-parser.y

z3-proof-parser.yy.c: z3-proof-parser.l z3-proof-parser.tab.h
	flex -o $@ z3-proof-parser.l

z3-proof-parser: z3-proof-parser.yy.c z3-proof-parser.tab.c z3-proof-parser.tab.h
	gcc -o z3-proof-parser z3-proof-parser.tab.c z3-proof-parser.yy.c

z3-proof-parser-sexpr.tab.c z3-proof-parser-sexpr.tab.h:	z3-proof-parser-sexpr.y
	bison -d z3-proof-parser-sexpr.y

z3-proof-parser-sexpr.yy.c: z3-proof-parser-sexpr.l z3-proof-parser-sexpr.tab.h
	flex -o $@ z3-proof-parser-sexpr.l

z3-proof-parser-sexpr: z3-proof-parser-sexpr.yy.c z3-proof-parser-sexpr.tab.c z3-proof-parser-sexpr.tab.h
	gcc -o z3-proof-parser-sexpr z3-proof-parser-sexpr.tab.c z3-proof-parser-sexpr.yy.c

proof_python: z3-proof-parser proof_unsat.py
	./proof_unsat.py > $@.txt
	./z3-proof-parser < $@.txt > $@.tex
	pdflatex $@.tex

proof_unsat: proof_unsat.cpp $(Z3DIR)
	g++ -o $@ $^ -lpthread -Wall

proof_cpp: z3-proof-parser-sexpr proof_unsat
	./proof_unsat > $@.txt
	./z3-proof-parser-sexpr < $@.txt > $@.tex
	pdflatex $@.tex

.PHONY: clean
clean:
	rm -rf z3-proof-parser z3-proof-parser.tab.c z3-proof-parser.tab.h z3-proof-parser.yy.c \
	z3-proof-parser-sexpr z3-proof-parser-sexpr.tab.c z3-proof-parser-sexpr.tab.h z3-proof-parser-sexpr.yy.c proof_unsat \
	proof_python.aux proof_python.log proof_python.tex proof_python.txt proof_python.pdf \
	proof_cpp.aux proof_cpp.log proof_cpp.tex proof_cpp.txt proof_cpp.pdf \
	*\~
