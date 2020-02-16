UNAME = $(shell uname)
WHO = $(shell whoami)
ifeq ($(UNAME), Linux)
	ifeq ($(WHO), jose.castellanosjoo)
	Z3DIR = /nfs/student/j/jose.castellanosjoo/Documents/GitProjects/z3__
	endif
	ifeq ($(WHO), jose)
# Z3DIR = /home/jose/Documents/Github\ Projects/z3
	Z3DIR = /home/jose/Documents/GithubProjects/z3__
	endif
Z3EXT = so
endif
ifeq ($(UNAME), Darwin)
Z3DIR = /Users/joseabelcastellanosjoo/Documents/Applications/z3__
Z3EXT = dylib
endif

IDIR = ./include
ODIR = ./obj
SDIR = ./src
CC = g++
FLAGS = -I$(IDIR) -std=c++11

SRC = $(wildcard $(SDIR)/*.cpp)
OBJS = $(patsubst $(SDIR)/%.cpp, $(ODIR)/%.o, $(SRC))
DEPS = $(wildcard $(IDIR)/*.h)

all: thcombination

$(ODIR)/%.o: $(SDIR)/%.cpp $(DEPS)
	$(CC) -g -c -o $@  $(FLAGS) $< -Wall

thcombination: $(OBJS) $(Z3DIR)/build/libz3.$(Z3EXT)
	$(CC) -g -o $@ $^ -lpthread -Wall

run: thcombination
	./thcombination

parser:
	make -C ../z3-proofs2latex

print_proof: ../z3-proofs2latex/z3-proof-parser-sexpr thcombination
	./thcombination > $@.txt
	$^ < $@.txt > $@.tex
	pdflatex $@.tex

.PHONY: clean_proof
clean_proof:
	rm print_proof*

.PHONY: clean
clean:
	rm -rf $(ODIR)/* thcombination print_proof*
