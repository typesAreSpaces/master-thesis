all: main

PAPER = main.tex
FILES = $(wildcard ./*.tex)

main: $(FILES)
	rubber --pdf $(PAPER)

.PHONY: clean
clean:
	rubber --clean $(PAPER)

	#rm -rf main.aux main.lof main.log main.lot main.out main.pdf main.toc \
	#*\~

