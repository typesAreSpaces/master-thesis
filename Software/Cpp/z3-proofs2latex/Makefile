all: print_proof

z3-proof-parser-sexpr.tab.c z3-proof-parser-sexpr.tab.h:	z3-proof-parser-sexpr.y
	bison -d z3-proof-parser-sexpr.y

z3-proof-parser-sexpr.yy.c: z3-proof-parser-sexpr.l z3-proof-parser-sexpr.tab.h
	flex -o $@ z3-proof-parser-sexpr.l

z3-proof-parser-sexpr: z3-proof-parser-sexpr.yy.c z3-proof-parser-sexpr.tab.c z3-proof-parser-sexpr.tab.h
	gcc -o z3-proof-parser-sexpr z3-proof-parser-sexpr.tab.c z3-proof-parser-sexpr.yy.c

../ThCombination/thcombination:
	make -C ../ThCombination

print_proof: ../ThCombination/thcombination z3-proof-parser-sexpr
	$^ > $@.txt
	./z3-proof-parser-sexpr < $@.txt > $@.tex
	pdflatex $@.tex

.PHONY: clean
clean:
	rm -rf \
	z3-proof-parser-sexpr z3-proof-parser-sexpr.tab.c z3-proof-parser-sexpr.tab.h z3-proof-parser-sexpr.yy.c proof_unsat \
	print_proof.aux print_proof.log print_proof.tex print_proof.txt print_proof.pdf \
	*\~
