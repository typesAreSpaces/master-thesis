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
OBJS = $(patsubst $(SDIR)/%.cpp, $(ODIR)/%.o, $(SRC))
DEPS = $(wildcard $(IDIR)/*.h)

TEST_DIR = /home/jose/Downloads/QF_UF/2018-Goel-hwbench
TEST_FILES = $(wildcard $(TEST_DIR)/*.smt2)
TEST_OUTPUT = $(patsubst $(TEST_DIR)/%.smt2, $(TEST_DIR)/%.txt, $(TEST_FILES))

all: tests/qf_uf_processing_test

$(ODIR)/%.o: $(SDIR)/%.cpp $(DEPS)
	$(CC) -g -c -o $@ $(FLAGS) $<

.PHONY: tests/qf_uf_processing_test
tests/qf_uf_processing_test: $(OBJS)
	$(CC) -g -c -o ./$@.o $(FLAGS) ./$@.cpp
	$(CC) -g -o $@ $(OBJS) $(Z3DIR)/build/libz3.$(Z3EXT) ./$@.o -lpthread
	rm -rf ./$@.o
	./$@.sh
	rm -rf $@

.PHONY: tests/old_general_test
tests/old_general_test:
	$(CC) -g -c -o ./$@.o $(FLAGS) ./$@.cpp
	$(CC) -g -o $@ $(OBJS) $(Z3DIR)/build/libz3.$(Z3EXT) ./$@.o -lpthread
	rm -rf ./$@.o

valgrind_run: euf_interpolator
	valgrind --log-file="euf_interpolator.txt" ./euf_interpolator

notes:
	grep -nr "// [A-Z][A-Za-z0-9]*: "

.PHONY: clean
clean:
	rm -rf $(ODIR)/* 

