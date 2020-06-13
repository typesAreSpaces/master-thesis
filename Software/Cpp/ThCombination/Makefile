UNAME = $(shell uname)
WHO = $(shell whoami)
ifeq ($(UNAME), Linux)
	ifeq ($(WHO), jose.castellanosjoo)
	Z3DIR = /nfs/student/j/jose.castellanosjoo/Documents/GitProjects/z3__
	endif
	ifeq ($(WHO), jose)
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
FLAGS = -I$(SDIR) -I$(IDIR) -std=c++11 -Wall

SRC = $(wildcard $(SDIR)/*.cpp)
OBJS = $(patsubst $(SDIR)/%.cpp, $(ODIR)/%.o, $(SRC)) $(Z3DIR)/build/libz3.$(Z3EXT) 
DEPS = $(wildcard $(IDIR)/*.h)

# ------------------------------------------------------------------------------------------
#  Build
all: tests/basic_test

$(ODIR)/%.o: $(SDIR)/%.cpp $(DEPS)
	$(CC) -g -c -o $@  $(FLAGS) $<
# ------------------------------------------------------------------------------------------
#  Tests

.PHONY: tests/basic_test
tests/basic_test: $(OBJS)
	$(CC) -g -c -o ./$@.o $(FLAGS) ./$@.cpp
	$(CC) -g -o $@ $(OBJS) ./$@.o -lpthread -Wall
	./$@
	rm -rf tests/*.o $@

# ------------------------------------------------------------------------------------------

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
