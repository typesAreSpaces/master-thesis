#Z3DIR = /home/jose/Documents/GithubProjects/z3/build/libz3.so

all: main

FILES = $(wildcard ./*.tex)

main: $(FILES)
	pdflatex $@.tex

.PHONY: clean
clean:
	rm -rf main.aux main.lof main.log main.lot main.out main.pdf main.toc \
	*\~

