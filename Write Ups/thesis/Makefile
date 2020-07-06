all: main

PAPER = main.tex
OUTPUT= $(PAPER:.tex=.pdf)
FILES = $(wildcard ./*.tex)

main: $(FILES)
	rubber --pdf $(PAPER)

.PHONY: clean
clean:
	rubber --clean $(PAPER)
	rm -rf $(OUTPUT) *\~

